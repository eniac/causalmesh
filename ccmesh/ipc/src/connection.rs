use anyhow::{bail, Result};
use bytes::{Buf, BytesMut};
use serde::{de::DeserializeOwned, Serialize};
use std::marker::PhantomData;
use tokio::io::{AsyncReadExt, AsyncWriteExt, BufStream};
use tracing::*;

// const BUF_SIZE: usize = 512;

#[derive(Debug, PartialEq, Eq)]
pub enum Encoding {
    Json,
    Bincode,
}

#[derive(Debug)]
pub struct Connection<T, U, const S: usize>
where
    T: Serialize + DeserializeOwned,
    U: AsyncReadExt + AsyncWriteExt + Unpin,
{
    pub id: usize,
    pub stream: BufStream<U>,
    pub buf: BytesMut,
    pub encoding: Encoding,
    pub working: bool,
    phantom: PhantomData<T>,
}

impl<T, U, const S: usize> Connection<T, U, S>
where
    T: Serialize + DeserializeOwned,
    U: AsyncReadExt + AsyncWriteExt + Unpin,
{
    pub fn new(id: usize, stream: U, encoding: Encoding) -> Connection<T, U, S> {
        Connection {
            id,
            stream: BufStream::new(stream),
            buf: BytesMut::with_capacity(S),
            encoding,
            phantom: PhantomData,
            working: true,
        }
    }

    pub async fn rebind(&mut self, stream: U, encoding: Encoding) -> Result<()> {
        if self.encoding != encoding {
            // self.encoding = encoding;
            bail!("Rebind connection with different encoding")
        }
        self.shutdown().await?;
        self.stream = BufStream::new(stream);
        self.working = true;
        Ok(())
    }

    async fn _read_frame(&mut self, size: u32) -> Result<T> {
        let size: usize = size.try_into().unwrap();
        loop {
            if self.buf.len() >= size {
                let buf = self.buf.split_to(size).freeze();
                match self.encoding {
                    Encoding::Json => {
                        return Ok(serde_json::from_slice(&buf).unwrap());
                    }
                    Encoding::Bincode => {
                        return Ok(bincode::deserialize(&buf).unwrap());
                    }
                }
            }
            let res = self.stream.read_buf(&mut self.buf).await;
            match res {
                Ok(0) => {
                    bail!(
                        "[Connection {}] closed with < `size` bytes in buffer",
                        self.id
                    )
                }
                Ok(_) => {
                    continue;
                }
                Err(e) => bail!("[Connection {}] read_buf error: {}", self.id, e),
            }
        }
    }

    async fn _read_size(&mut self) -> Result<Option<u32>> {
        loop {
            if self.buf.len() >= std::mem::size_of::<u32>() {
                let size = self.buf.get_u32();
                assert!(size > 0);
                let cap = self.buf.capacity();
                if size >= cap.try_into().unwrap() {
                    self.buf.reserve(cap);
                    debug!("[Connection {}] extend buffer to {}", self.id, cap * 2);
                }
                return Ok(Some(size));
            }
            let res = self.stream.read_buf(&mut self.buf).await;
            match res {
                Ok(0) => {
                    if self.buf.is_empty() {
                        return Ok(None); // EOF
                    } else {
                        bail!(
                            "[Connection {}] closed with < sizeof(u32) bytes in buffer",
                            self.id
                        )
                    }
                }
                Ok(_) => continue,
                Err(e) => bail!("[Connection {}] read_buf error: {}", self.id, e),
            }
        }
    }

    pub async fn read_frame(&mut self) -> Result<Option<T>> {
        assert!(self.working);
        let size = self._read_size().await?;
        if size.is_none() {
            self.shutdown().await?;
            return Ok(None); // EOF
        }
        let frame = self._read_frame(size.unwrap()).await?;
        Ok(Some(frame))
    }

    // Flush not called by default
    pub async fn write_frame(&mut self, frame: &T) -> Result<()> {
        assert!(self.working);
        let buf = match self.encoding {
            Encoding::Json => serde_json::to_vec(&frame).unwrap(),
            Encoding::Bincode => bincode::serialize(&frame).unwrap(),
        };
        let size = buf.len().try_into().unwrap();
        self.stream.write_u32(size).await?;
        self.stream.write_all(&buf).await?;
        Ok(())
    }

    pub async fn flush(&mut self) -> Result<()> {
        self.stream.flush().await?;
        Ok(())
    }

    pub async fn write_frame_and_flush(&mut self, frame: &T) -> Result<()> {
        self.write_frame(frame).await?;
        self.flush().await?;
        Ok(())
    }

    pub async fn shutdown(&mut self) -> Result<()> {
        self.working = false;
        if !self.buf.is_empty() {
            self.buf.clear();
            debug!(
                "[Connection {}] shutdown while buffer is not empty",
                self.id
            );
        }
        self.stream.shutdown().await.unwrap();
        Ok(())
    }
}

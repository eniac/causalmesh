#!/bin/bash -x

curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
source $HOME/.cargo/env
sudo add-apt-repository -y ppa:redislabs/redis
sudo apt update
sudo apt install -y redis-server
curl -OL https://go.dev/dl/go1.17.8.linux-amd64.tar.gz
sudo tar -C /usr/local -xvf go1.17.8.linux-amd64.tar.gz
rm go1.17.8.linux-amd64.tar.gz
echo "export PATH=$PATH:/usr/local/go/bin" >> $HOME/.bashrc
source $HOME/.bashrc

sudo apt install -y build-essential cmake mosh htop zip libssl-dev pkg-config net-tools zlib1g-dev tmux
cd $HOME
git clone --recurse-submodules https://github.com/ut-osa/nightcore.git
cd $HOME/nightcore/deps/abseil-cpp
git checkout lts_2022_06_23
cd $HOME/nightcore
sed -i 's/-Werror//g' Makefile
./build_deps.sh
make -j4

cargo install oha
ulimit -n 8000
cd $HOME

PB_REL="https://github.com/protocolbuffers/protobuf/releases"
curl -LO $PB_REL/download/v3.15.8/protoc-3.15.8-linux-x86_64.zip
sudo unzip protoc-3.15.8-linux-x86_64.zip -d /usr/local
rm protoc-3.15.8-linux-x86_64.zip

sudo chmod 777 -R /usr/local/

git clone https://github.com/giltene/wrk2.git
cd wrk2
make -j4
cd ..

cd ccmesh
cargo build --release
cd ..

sudo usermod -s /bin/bash $USER
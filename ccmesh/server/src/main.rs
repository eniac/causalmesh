use clap::Parser;
use hz_con::service::run as con_run;
use hz_config::*;
use hz_mesh::service::run as mesh_run;
use hz_opt::service::run as opt_run;
use hz_cb::service::run as cb_run;
use hz_faas::service::run as faas_run;
use std::io::Write;
use sysinfo::{ProcessExt, ProcessRefreshKind, RefreshKind, System, SystemExt};

#[derive(Parser)]
#[clap(author, version, about, long_about = None)]
struct ServerCli {
    #[clap(value_parser)]
    id: usize,
}

fn monitor() {
    let mut s = System::new_with_specifics(
        RefreshKind::new().with_processes(ProcessRefreshKind::everything()),
    );
    s.refresh_all();
    let _ = std::fs::remove_file("monitor.txt");
    let mut file = std::fs::OpenOptions::new()
        .write(true)
        .create(true)
        .append(true)
        .open("monitor.txt")
        .unwrap();
    loop {
        let mut pids = vec![];
        for process in s.processes_by_name("hz-server") {
            let res = format!(
                "{} {}\n",
                process.cpu_usage(),
                process.memory() / 1024 / 1024
            );
            file.write_all(res.as_bytes()).unwrap();
            pids.push(process.pid());
        }
        assert_eq!(pids.len(), 1);
        s.refresh_process_specifics(pids[0], ProcessRefreshKind::everything());
        std::thread::sleep(std::time::Duration::from_secs(1));
    }
}

#[tokio::main(flavor = "current_thread")]
async fn main() {
    tracing_subscriber::fmt::init();
    let cli = ServerCli::parse();
    if cli.id == 0 {
        let builder = std::thread::Builder::new().name("hz-monitor".into());
        builder.spawn(monitor).unwrap();
    }
    if MODE == "mesh" {
        mesh_run(cli.id).await;
    } else if MODE == "opt" {
        opt_run(cli.id).await;
    } else if MODE == "con" {
        con_run(cli.id).await;
    } else if MODE == "cb" {
        cb_run(cli.id).await;
    } else if MODE == "faas" {
        faas_run(cli.id).await;
    } else {
        panic!("unknown mode");
    }
}

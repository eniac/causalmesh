import time
import signal
import json
import argparse

from fabric import Connection, ThreadingGroup
from common import HOST_SERVERS, KEY_FILE
from statistics import median
from pprint import pprint

HZ_SERVERS = HOST_SERVERS[1:-1]

ALG = ""
TOOL = "oha"
SCALE_LAMBDA = False

def redis_conn():
    return Connection(HOST_SERVERS[0], connect_kwargs={
        'key_filename': KEY_FILE,
    })


def server_group():
    group = ThreadingGroup(*HZ_SERVERS, connect_kwargs={
        'key_filename': KEY_FILE,
    })
    return group


def server_conn(idx):
    return Connection(HZ_SERVERS[idx], connect_kwargs={
        'key_filename': KEY_FILE,
    })


def scheduler_conn():
    return Connection(HOST_SERVERS[-1], connect_kwargs={
        'key_filename': KEY_FILE,
    })


def custom_conn(addr):
    return Connection(addr, connect_kwargs={
        'key_filename': KEY_FILE,
    })


def build_redis():
    redis = redis_conn()
    res = redis.run("cd ~/ccmesh && ~/.cargo/bin/cargo build --release --bin redis", asynchronous=True, pty=True)
    return [res]


def build_servers():
    res = []
    for idx in range(len(HZ_SERVERS)):
        s = server_conn(idx)
        r = s.run(f"cd ~/ccmesh && ~/.cargo/bin/cargo build --release --bin hz-server", asynchronous=True, pty=True)
        res.append(r)
    return res


def build_scheduler():
    s = scheduler_conn()
    res1 = s.run("cd ~/ccmesh && ~/.cargo/bin/cargo build --release --bin scheduler", asynchronous=True, pty=True)
    res2 = s.run("cd ~/ccmesh && ~/.cargo/bin/cargo build --release --bin vis", asynchronous=True, pty=True)
    return [res1, res2]


def build_all():
    res = []
    res += build_redis()
    res += build_servers()
    res += build_scheduler()
    for r in res:
        out = r.join()
        assert out.exited == 0


def start_redis():
    redis = redis_conn()
    res = redis.run("cd ~/ccmesh && ~/.cargo/bin/cargo run --release --bin redis", asynchronous=True, pty=True)
    return res


def start_server(idx):
    s = server_conn(idx)
    res1 = s.run(f"cd ~/ccmesh && ~/.cargo/bin/cargo run --release --bin hz-server {idx}", asynchronous=True, pty=True)
    res2 = s.run(f"cd ~/ccmesh-go && bash {ALG}.sh", asynchronous=True, pty=True)
    return res1, res2


def start_scheduler():
    s = scheduler_conn()
    res = s.run("cd ~/ccmesh && ~/.cargo/bin/cargo run --release --bin scheduler", asynchronous=True, pty=True)
    return res


def cut_until_release(s: str):
    res = []
    flag = False
    for line in s.split():
        if line.strip() == "":
            continue
        if flag:
            res.append(line)
        if "target/release" in line:
            flag = True
    return " ".join(res)


def prepare():
    futs = []
    futs.append(start_redis())
    time.sleep(1)
    for idx in range(len(HZ_SERVERS)):
        res = start_server(idx)
        futs.append(res[0])
        futs.append(res[1])
    futs.append(start_scheduler())
    time.sleep(5)
    return futs


def parse_oha(output):
    res = {}
    for line in output.splitlines():
        line = line.strip()
        if "50.00%" in line:
            v = "{:.1f}".format(float(line.split()[3]) * 1000)
            res["50%"] = v
        elif "95.00%" in line:
            v = "{:.1f}".format(float(line.split()[3]) * 1000)
            res["95%"] = v
        elif "99.00%" in line:
            v = "{:.1f}".format(float(line.split()[3]) * 1000)
            res["99%"] = v
    return res


def parse_wrk(output):
    res = {}
    for line in output.splitlines():
        line = line.strip()
        if line.startswith("50.000%"):
            v = line.split()[1]
            if v.endswith("ms"):
                v = v[:-2]
            else:
                v = None
            res["50%"] = v
        elif line.startswith("99.000%"):
            v = line.split()[1]
            if v.endswith("ms"):
                v = v[:-2]
            else:
                v = None
            res["99%"] = v
    return res


def oha(rps, duration) -> str:
    return f"~/.cargo/bin/oha -q {rps} -z {duration}s --latency-correction --disable-keepalive --no-tui http://127.0.0.1:3000"


def oha_addr(rps, duration, addr) -> str:
    return f"~/.cargo/bin/oha -q {rps} -z {duration}s --latency-correction --disable-keepalive --no-tui http://{addr}:3000"


def wrk(rps, duration) -> str:
    return f"./wrk2/wrk -t2 -c64 -d{duration}s -R{rps} --latency http://127.0.0.1:3000"


def wrk_seq(rps, duration) -> str:
    return f"./wrk2/wrk -t1 -c16 -d{duration}s -R{rps} --latency http://127.0.0.1:3000"


def run_once(rps, warmup=10):
    assert ALG in ["mesh", "con", "opt", "cb", "media", "faas"]
    redis = redis_conn()
    redis.run("echo FLUSHALL | redis-cli", hide=True)
    time.sleep(2)
    print("Building...", end=", ")
    build_all()
    print("Preparing...", end=", ")
    futs = prepare()
    client = scheduler_conn()
    dura = 120
    if warmup > 0:
        print("Warming up...", end=", ")
        if TOOL == "oha":
            client.run(oha(rps, warmup), hide=True)
        else:
            client.run(wrk(rps, warmup), hide=True)
    if ALG == "media":
        time.sleep(5)
    time.sleep(3)
    print("Evaluating...", end=", ")
    if SCALE_LAMBDA:
        output = client.run(wrk_seq(rps, dura), hide=True)
        res = parse_wrk(output.stdout)
    else:
        if TOOL == "oha":
            output = client.run(oha(rps, dura), hide=True)
            res = parse_oha(output.stdout)
        else:
            output = client.run(wrk(rps, dura), hide=True)
            res = parse_wrk(output.stdout)
    # print(ALG, end=", ")
    # print(rps, end=", ")
    # pprint(res)
    print("Cleaning...")
    try:
        for f in futs:
            f.runner.send_interrupt(signal.SIGINT)
        try:
            futs[-1].join()
        except Exception as e:
            print(cut_until_release(e.result.stdout))
        try:
            futs[1].join()
        except Exception as e:
            print(cut_until_release(e.result.stdout))
    except Exception as e:
        print(e)
    redis = redis_conn()
    redis.run("echo FLUSHALL | redis-cli", hide=True)
    cpu, mem = read_cpu_mem()
    time.sleep(1)
    res["cpu"] = "{:.1f}".format(cpu)
    res["mem"] = "{:.1f}".format(mem)
    return res

def run_con():
    global ALG
    ALG = "con"
    print("con")
    rpss = [1000, 2000, 3000, 4000, 5000, 6000]
    rpss = [300, 600, 900, 1200, 1500, 1800, 2100, 2400, 2700, 3000]
    rpss = [1000, 1500, 2000, 2500, 3000, 3500, 4000, 4500, 5000, 5500, 6000]
    for rps in rpss:
        res = run_once(rps, warmup=30)
        print(rps, end=", ")
        print(res)


def run_opt():
    print("opt")
    global ALG
    ALG = "opt"
    rpss = [1000, 2000, 3000, 4000, 5000, 6000]
    rpss = [1000, 1500, 2000, 2500, 3000, 3500, 4000, 4500, 5000, 5500, 6000]
    for rps in rpss:
        res = run_once(rps, warmup=30)
        print(rps, end=", ")
        print(res)


def run_cb():
    print("cb")
    global ALG
    ALG = "cb"
    rpss = [3000]
    for rps in rpss:
        res = run_once(rps, warmup=30)
        print(rps, end=", ")
        print(res)


def run_mesh():
    print("mesh")
    global ALG
    ALG = "mesh"
    rpss = [1000, 2000, 3000, 4000, 5000, 6000, 7000, 8000]
    rpss = [1000, 1500, 2000, 2500, 3000, 3500, 4000, 4500, 5000, 5500, 6000]
    rpss = [1000]
    for rps in rpss:
        res = run_once(rps, warmup=30)
        print(rps, end=", ")
        print(res)

def run_faas():
    print("faas")
    global ALG
    ALG = "faas"
    rpss = [1000, 1500, 2000, 2500, 3000, 3500, 4000]
    rpss = [2000]
    for rps in rpss:
        res = run_once(rps, warmup=30)
        print(rps, end=", ")
        print(res)

def run_media1():
    global ALG
    ALG = "media"
    # print("con")
    rpss = [300, 600, 900, 1200, 1500, 1800, 2100, 2400, 2700, 3000]
    for rps in rpss:
        res = run_once(rps, warmup=30)
        print(rps, end=", ")
        print(res)


def run_media2():
    global ALG
    ALG = "media"
    rpss = [600, 900, 1200, 1500, 1800, 2100, 2400, 2700, 3000, 3300, 3600]
    for rps in rpss:
        res = run_once(rps, warmup=30)
        print(rps, end=", ")
        print(res)


def read_cpu_mem():
    s = server_conn(0)
    res = s.run("cd ~/ccmesh && cat monitor.txt", hide=True)
    res = res.stdout
    lines = res.splitlines()
    lines = lines[-10:]
    cpus = []
    mems = []
    for line in lines:
        line = line.strip()
        cpu, mem = line.split()
        cpus.append(float(cpu))
        mems.append(float(mem))
    return sum(cpus) / len(cpus), sum(mems) / len(mems)


def run_and_hang(sec):
    global ALG
    ALG = "mesh"
    redis = redis_conn()
    redis.run("echo FLUSHALL | redis-cli", hide=True)
    time.sleep(2)
    print("Building...", end=", ")
    build_all()
    print("Preparing...", end=", ")
    futs = prepare()
    print("Running...", end=", ")
    time.sleep(sec)
    print("Cleaning...")
    for f in futs:
        f.runner.send_interrupt(signal.SIGINT)
    for f in futs:
        try:
            f.join()
        except Exception as e:
            print(cut_until_release(e.result.stdout))
    redis = redis_conn()
    redis.run("echo FLUSHALL | redis-cli", hide=True)


def generate_table():
    ls = {}
    alg = ""
    with open("a") as f:
        lines = f.readlines()
        for line in lines:
            if "con" in line or "opt" in line or "mesh" in line:
                alg = line.strip()
            if "mem" in line:
                ks = line.split(",")
                rps = int(ks[0])
                rest = ",".join(ks[1:]).strip()
                rest = rest.replace("'", '"')
                data = json.loads(rest)
                ls[rps] = data
    print("3 Lambdas", end="\t")
    for k in ls.keys():
        print(k, end="\t")
    print()
    ks = sorted(ls.keys())
    print(f"P50 ({alg})", end="\t")
    for k in ks:
        print(ls[k]["50%"], end="\t")
    print()
    print("P95", end="\t")
    for k in ks:
        print(ls[k]["95%"], end="\t")
    print()
    print("P99", end="\t")
    for k in ks:
        print(ls[k]["99%"], end="\t")
    print()
    print("CPU", end="\t")
    for k in ks:
        print(ls[k]["cpu"], end="\t")
    print()
    print("Mem(MB)", end="\t")
    for k in ks:
        print(ls[k]["mem"], end="\t")
    print()


def run_scale_lambda():
    print(ALG)
    res = run_once(100, warmup=30)
    print(res)


def run_scale_server():
    print(ALG)
    res = run_once(1, warmup=10)
    print(res)


def run_vis():
    global ALG
    ALG = "mesh"
    redis = redis_conn()
    redis.run("echo FLUSHALL | redis-cli", hide=True)
    time.sleep(2)
    print("Building...", end=", ")
    build_all()
    print("Preparing...", end=", ")
    futs = prepare()
    print("Running...", end=", ")

    scheduler = scheduler_conn()
    res = scheduler.run("cd ~/ccmesh && ~/.cargo/bin/cargo run --release --bin vis", asynchronous=True, pty=True)
    time.sleep(3)
    try:
        res.runner.send_interrupt(signal.SIGINT)
    except Exception as e:
        print(res.join())
    try:
        res.join()
    except Exception as e:
        res = cut_until_release(e.result.stdout)
        duras = []
        for line in res.split():
            if line.isnumeric():
                duras.append(int(line))
        print()
        print("Window: ", end="")
        print(median(duras))
    for f in futs:
        f.runner.send_interrupt(signal.SIGINT)
    for f in futs:
        try:
            f.join()
        except Exception as e:
            print(cut_until_release(e.result.stdout))
    redis = redis_conn()
    redis.run("echo FLUSHALL | redis-cli", hide=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--alg", type=str, default="")
    parser.add_argument("--exp", type=str, required=True)
    args = parser.parse_args()
    global ALG
    ALG = args.alg
    if args.exp == "vis":
        run_vis()
    if args.exp == "scale_lambda":
        global SCALE_LAMBDA
        SCALE_LAMBDA = True
        run_scale_lambda()
    if args.exp == "scale_server":
        run_scale_server()
    if args.exp == "media":
        run_media2()
    if args.exp == "micro":
        if ALG == "mesh":
            run_mesh()
        if ALG == "con":
            run_con()
        if ALG == "opt":
            run_opt()
        if ALG == "faas":
            run_faas()
    # run_and_hang(180)
    # run_media1()
    # run_media2()
    # run_mesh()
    # generate_table()
    # run_con()
    # run_opt()
    # run_cb()
    pass


if __name__ == '__main__':
    main()

# CausalMesh

This repository contains the prototype system for our VLDB 2025 paper:
[CausalMesh: A Causal Cache for Stateful Serverless Computing](https://www.cis.upenn.edu/~sga001/papers/causalmesh-vldb25.pdf).

It also contains code from our extended report which includes a formal verification of the protocol in Dafny.
The report is available [here](https://arxiv.org/pdf/2508.15647).


## Project Structure
```
ccmesh/ - Server code
  causal/ - define vector clock (VC), happens-before relationship, and all causal consistency related functions
  redis/ - causal layer on top of redis
  ipc/ - data serialization and transmission
  scheduler/ - a naive scheduler that randomly schedules functions to different compute nodes
  workload/ - microbenchmark and a real-world application (media app) used in evaluation
  # The following 4 folders implement server APIs defined in Table 4 in the paper
  ccmesh/ - causalmesh server logic
  con/ - hydrocache-con server logic
  opt/ - hydrocache-opt server logic
  faas/ - faasTCC server logic

ccmesh-go/ - Client code in golang, clients are compiled to binary and registered in Nightcore (https://github.com/ut-osa/nightcore)
  the following 4 caches implement Client APIs defined in Section 5.1
  pkg/ccmesh - causalmesh client library (Section 6)
  pkg/hzcon - hydrocache-con client library
  pkg/hzopt - hydrocache-opt client library
  pkg/hzfass - FaaSTCC client library


causal-tla/ - TLA+ model
  mesh.tla - model checking code
  prood.md - lammas and invariants explained in plain English
```

## Experiment Setup (w/ Cloudlab)

### CausalMesh Server

#### Prerequisites
Clone both the server code (ccmesh) and the client code (ccmesh-go) in the same directory, fill in the location of the directory, key file location and cloudlab user name in scripts/common.py

Install Python 3 and fabric
```
pip install fabric
```

#### Setup
Use the following profile to create a cluster on Cloudlab
```
https://www.cloudlab.us/p/a22d79e1ff06310e24e133d03acc1703ec3b09ad
```

Copy the hostname of the nodes to `scripts/common.py`.

Run on the host
```
python scripts/upload.py
python scripts/setup.py
```

After setup finishes on all server, log in the first machine on cloudlab (10.10.1.1)

```
# on 10.10.1.1
sudo sed -i 's/bind 127.0.0.1 -::1//g' /etc/redis/redis.conf
sudo service redis-server restart
echo "CONFIG SET protected-mode no" | redis-cli
```

### Run experiments
To run Causalmesh, HydroCache-Con and HydroCache-Opt

change feature flags in `Cargo.toml` to
```
default = ["ccmesh", "cloud"]
```
```
default = ["con", "cloud"]
```
```
default = ["opt", "cloud"]
```
respectively, then run
```
python scripts/upload.py
```

All following commands should be run on the host.

#### Microbenchmarks
```
python scripts/run.py --alg ccmesh --exp micro
python scripts/run.py --alg con --exp micro
python scripts/run.py --alg opt --exp micro
```

#### Real world application
```
python scripts/run.py --alg ccmesh --exp media
python scripts/run.py --alg opt --exp media
```

#### Various length of workflow
```
python scripts/run.py --alg ccmesh --exp scale_lambda
```

#### Various number of cache server
```
python scripts/run.py --alg ccmesh --exp scale_server
```

#### Visibility
```
python scripts/run.py --alg ccmesh --exp vis
```

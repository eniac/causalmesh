Tested on Ubuntu 20.

1. Run `bash install_assets.sh` to extract Dafny-3.4 and DotNet-6 from assets.

2. Create python virtual environment and install scons:
```
sudo apt install python3-venv

python3 -m venv .venv

source .venv/bin/activate 

pip3 install scons
```

3. Change paths in config.json, note you cannot use ~ for home path here

4. Run 'python3 compile.py' to compile
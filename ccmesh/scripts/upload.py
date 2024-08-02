import argparse
import subprocess
from common import CLOUD, SERVERS, WS_DIR, CLOUDLAB_USER

def run_collect_output(cmd):
    res = subprocess.run(cmd, stdout=subprocess.PIPE)
    return res.stdout.decode('utf-8').strip()

def run_shell(cmd):
    res = subprocess.run(cmd, stdout=subprocess.PIPE, shell=True)
    return res.stdout.decode('utf-8').strip()

def cloudlab():
    for s in SERVERS:
        print("copying files to ", s)
        path = f'{CLOUDLAB_USER}@{s}:~/'
        run_collect_output(['rsync', '--exclude', 'target', '--exclude', 'figures', '-r', f'{WS_DIR}/ccmesh', path])
        run_collect_output(['rsync', '-r', f'{WS_DIR}/ccmesh-go', path])

def main():
    cloudlab()


if __name__ == '__main__':
    main()

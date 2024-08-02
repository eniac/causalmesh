from fabric import Connection, ThreadingGroup
from common import HOST_SERVERS, KEY_FILE


def setup():
    group = ThreadingGroup(*HOST_SERVERS, connect_kwargs={
        'key_filename': KEY_FILE,
    })
    res = group.run("bash ccmesh/scripts/setup.sh")
    print(res)


def main():
    setup()


if __name__ == '__main__':
    main()

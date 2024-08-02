NSERVERS = 5

WS_DIR = '' # location of ccmesh and ccmesh-go
KEY_FILE = '' # location of ssh key file
CLOUDLAB_USER = '' # username on cloudlab

MSSERVERS = [1205, 1307, 1214]
MSSERVERS = MSSERVERS[:NSERVERS + 2]
SERVERS = [f'ms{s}.utah.cloudlab.us' for s in MSSERVERS]
HOST_SERVERS = [f'{CLOUDLAB_USER}@{s}' for s in SERVERS]

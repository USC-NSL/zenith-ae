import pymongo


# Path for standalone MongoDB deployement
LOCAL_STANDALONE_PATH = "mongodb://localhost:27017/"

# Path for replicated MongoDB deployement
LOCAL_REPLICATED_PATH = "mongodb://127.0.0.1:27017/?directConnection=true&serverSelectionTimeoutMS=2000"

# Path format for standalone MongoDB deployement
STANDALONE_PATH_FMT = "mongodb://{host}:{port}"

# Path format for replicated MongoDB deployement
REPLICATED_PATH_FMT = "mongodb://{host}:{port}/?directConnection=true&serverSelectionTimeoutMS=2000"

# Name of the replica set
REPLICA_SET_NAME = "nibRS"

# Default read/write concerns
DEFAULT_READ_CONCERN = pymongo.read_concern.ReadConcern("local")
DEFAULT_WRITE_CONCERN = pymongo.write_concern.WriteConcern("majority", wtimeout=1000)
DEFAULT_READ_PREFERENCE = pymongo.ReadPreference.SECONDARY_PREFERRED

# If True, log messages only show the 2 LSBs of ObjectIds from Mongo
USE_SHORT_ID = True

# If True, db.watch() operations will be used instead of polling,
# much better for NIBs health
USING_REPLICATION = False

if USING_REPLICATION:
	LOCAL_PATH = LOCAL_REPLICATED_PATH
else:
	LOCAL_PATH = LOCAL_STANDALONE_PATH

# Disables all NIB transactions, meaning that an arbitrary delay
# may happen between any two consecutive NIB operations
# By default this behavior is enabled, it is one of the main points
# of our implementation.
DISABLE_TRANSACTIONS = True

# RabbitMQ host
DEFAULT_RBQ_HOST = "127.0.0.1"
DEFAULT_RBQ_USER = "docker"
DEFAULT_RBQ_PASS = "docker"

# Queue types
class QueueTypes:
	STANDARD = "standard"
	QUORUM = "quorum"

# RBQ prefetch count (depends on the system ...)
DEFAULT_PREFETCH_COUNT = 1

# If False, all logging is completely disabled.
DO_LOGGING = True

# Group IRs start from this cookie value
GROUP_IR_START_COOKIE = 30000

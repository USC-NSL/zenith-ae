import pika
import subprocess
from pynadir.utils.logging import TitledLog
from nib.nib_defs import COLLECTIONS
from nib.nib_direct import NIBDirect
from nib.nib_settings import DEFAULT_RBQ_HOST, DEFAULT_RBQ_USER, DEFAULT_RBQ_PASS


"""
AMQP defines no method for actually discovering queues bound to a exchange, so the
only thing that we can do is just query all queues and blow them up.
This of course needs to be done local to the broker instance.
"""
RBQ_ADMIN_GET_QUEUES = "rabbitmqadmin list queues name"


def _get_queues():
	res = subprocess.getoutput(RBQ_ADMIN_GET_QUEUES)
	lines = res.split('\n')[3:-1]
	return [line.replace('|', '').strip() for line in lines]


def nuke_db(nib_path=None, db_name='nib'):
	"""
	Delete everything on the NIB DB
	"""

	direct = NIBDirect(nib_path, db_name)
	direct.clear_all()


def nuke_broker(broker_host=None, broker_user=None, broker_pass=None, exchange_name="NIB"):
	"""
	Delete everything on the NIB broker
	"""

	broker_host = broker_host if broker_host else DEFAULT_RBQ_HOST
	broker_user = broker_user if broker_user else DEFAULT_RBQ_USER
	broker_pass = broker_pass if broker_pass else DEFAULT_RBQ_PASS

	con = pika.BlockingConnection(pika.ConnectionParameters(broker_host, credentials=pika.PlainCredentials(
		broker_user,
		broker_pass
	)))

	ch = con.channel()

	queues = _get_queues()
	for queue in queues:
		if queue.startswith(COLLECTIONS.TE_EVENT) or queue.startswith(COLLECTIONS.IR_QUEUE):
			ch.queue_delete(queue=queue)

	ch.exchange_delete(exchange=exchange_name)
	ch.close()
	con.close()

	TitledLog.warning('nib', f"Cleared {exchange_name} broker")


def nuke(nib_path=None, db_name='nib', nib_broker_host=None, nib_broker_user=None, nib_broker_pass=None, exchange_name="NIB"):
	nuke_db(nib_path, db_name)
	nuke_broker(nib_broker_host, nib_broker_user, nib_broker_pass, exchange_name)


if __name__ == '__main__':
	nuke()
	
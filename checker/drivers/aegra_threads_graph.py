"""The graph Aegra loads for `drivers.aegra_threads`, named in its generated `aegra.json`."""

import os

from drivers import aegra_threads

graph = aegra_threads.hosted_graph(os.environ["AEGRA_THREADS_VERSION"])

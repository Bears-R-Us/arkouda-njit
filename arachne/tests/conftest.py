import pytest

def pytest_addoption(parser):
    parser.addoption(
        "--server-host",
        action="store",
        default=None,
        help="Hostname or IP of an already-running arkouda_server"
    )
    parser.addoption(
        "--server-port",
        action="store",
        default=None,
        type=int,
        help="Port of an already-running arkouda_server"
    )

def pytest_configure(config):
    server_host = config.getoption("--server-host")
    server_port = config.getoption("--server-port")

    if server_host is None or server_port is None:
        raise pytest.UsageError(
            "You must specify both --server-host and --server-port when running the tests."
        )

    # Save them globally to be used by the tests.
    import builtins
    builtins.SERVER_HOST = server_host
    builtins.SERVER_PORT = server_port

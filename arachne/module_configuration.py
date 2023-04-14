# This file is designed to provide a user with the commands required to configure their external module.
# NOTE - this file will not automatically execute any commands, the user must manually copy the commands and run them.
# TODO - add option to export commands to shell script

# Currently export of PYTHONPATH is only functional when run manually or source file.sh.

import os
import optparse
import glob
import time
import pkg_resources as pr

PIP_INSTALLS = []
USER_MODS = []
ADD_TO_CONFIG = []


def install_client_pkg(client_path):
    """
    Add client path to list of packages to be pip installed

    Parameters
    __________
        client_path: absolute path to python package
    """
    global PIP_INSTALLS

    PIP_INSTALLS.append(client_path)


def get_server_modules(cfg):
    """
    Get list of modules to add at users request.

    Parameters
    __________
        cfg: ServerModules.cfg path for the module being added.

    Returns
    _______
        List of module names that need to be added to the main .cfg file to be built
    """
    mod_list = []
    with open(cfg) as f:
        for line in f.readlines():
            m = line.split("#")[0].strip()
            mod_list += [m] if m else []
    return mod_list


def get_chpl_files(mod_path):
    """
    Get the chapel files that need to be compiled for the provided package

    Parameters
    __________
        mod_path: path to the module being added to the server.

    Returns
    ______
        List of .chpl files at mod_path/server
    """
    path = mod_path + "/server/*.chpl"
    return glob.glob(path)


def configure_server_module(mod_path):
    """
    Configure elements that need to be added to the server for the provided module to be built

    Parameters
    __________
        mod_path: Path to the package.

    """
    global ADD_TO_CONFIG, USER_MODS

    mod_cfg = mod_path + "/server/ServerModules.cfg"
    # ak_cfg = ak_loc + "/ServerModules.cfg"

    # get all of the modules listed in the .cfg file
    mods = get_server_modules(mod_cfg)
    for mod in mods:
        ADD_TO_CONFIG.append(f" {mod_path}/server/{mod}.chpl")


def validate_pkgs(pkg_list, ak_loc):
    """
    Validate that all packages are configured as required and provide errors if not

    Parameters
    __________
        pkg_list: List of full paths to packages
        ak_loc: string path to arkouda

    Raises
    ______
        RuntimeError: If any configuration is incorrect.

    Notes
    _____
        Validation is run on all packages at once. This prevents partial installations and quickly alerts the user to
        any issues.
    """
    # Pip is required to install client pkgs, verify if is installed.
    installed_pkgs = {pkg.key for pkg in pr.working_set}
    if 'pip' not in installed_pkgs:
        raise RuntimeError("pip is required for the client installation. Please install pip.")

    ak_checked = False
    for pkg in pkg_list:
        # Verify that the pkg path exists
        if not os.path.exists(pkg):
            raise RuntimeError(f"Package Not Found. {pkg} does not exist.")
        client_path = pkg + "/client"
        server_path = pkg + "/server"
        # Verify the client package configuration
        if not os.path.exists(client_path):
            raise RuntimeError(f"Invalid package. Client package not found. {pkg}")
        if not os.path.exists(client_path + "/setup.py"):
            raise RuntimeError(f"Invalid Package Configuration. Missing setup.py. {pkg}")

        # Verify the server module configuration
        if os.path.exists(server_path):
            # If the arkouda location has not yet been checked, validate it exists.
            if not ak_checked:
                if ak_loc:
                    if not os.path.exists(ak_loc):
                        raise RuntimeError(f"Arkouda Location not provided or invalid. Set using --ak argument."
                                           f" Provided: {ak_loc}")
                    ak_cfg = ak_loc + "/ServerModules.cfg"
                    if not os.path.exists(ak_cfg):
                        raise RuntimeError(f"Could not locate arkouda ServerModules.cfg: {ak_cfg}")
                else:
                    raise RuntimeError(f"Arkouda Location not provided or invalid. Set using --ak argument."
                                       f" Provided: {ak_loc}")
                ak_checked = True

            # Verify that ServerModules.cfg exists for the module
            mod_cfg = server_path + "/ServerModules.cfg"
            if not os.path.exists(mod_cfg):
                raise RuntimeError(f"Could not locate module ServerModules.cfg: {mod_cfg}")


def create_commands(ak_loc, config_loc):
    """
    Creates the commands needed to install the client packages and make the server with the supplied modules.

    Parameters
    __________
        ak_loc: Path to arkouda
        config_loc: Path to the directory where temporary .cfg files are stored. Defaults to ~ (users home directory)

    Notes
    _____
        All commands are printed. Execution can be triggered by piping the script execution to bash.
    """
    # install clients or Update if already installed
    print(f"pip install -U {' '.join(PIP_INSTALLS)}")

    # Create modified config file with user modules - .cfg saved to user home directory
    ak_cfg = ak_loc + "/ServerModules.cfg"
    tmp_cfg = f"{config_loc}/TmpServerModules.cfg.{int(time.time())}"
    print(f"cp {ak_cfg} {tmp_cfg}")

    ak_srv_user_mods = '"' + " ".join(ADD_TO_CONFIG) + '"'  # setup our ARKOUDA_SERVER_USER_MODULES
    print(f"ARKOUDA_SERVER_USER_MODULES={ak_srv_user_mods} ARKOUDA_CONFIG_FILE={tmp_cfg} "
          f"ARKOUDA_SKIP_CHECK_DEPS=true make -C {ak_loc}")


def run(pkg_list, ak_loc, config_loc):
    """
    Main function used for installing packages. Validation, configuration, and printing commands triggered from here.

    Parameters
    __________
        pkg_list: List of paths to packages to be installed/added to the server.
        ak_loc: Path to arkouda
        config_loc: Path to the directory where the user would like .cfg files stored.
    """
    # If only single pkg being installed, convert to list
    if isinstance(pkg_list, str):
        pkg_list = [pkg_list.rstrip("/")]

    # All packages reviewed at once. This prevents partial installs and alerts user to issues sooner.
    validate_pkgs(pkg_list, ak_loc)

    # Configure the components needed to build install commands
    for pkg in pkg_list:
        pkg = pkg.rstrip("/")  # remove trailing slash
        if ak_loc:
            ak_loc = ak_loc.rstrip("/")  # remove trailing slash

        client_path = pkg + "/client"
        server_path = pkg + "/server"

        install_client_pkg(client_path)
        if os.path.exists(server_path):
            configure_server_module(pkg)

    create_commands(ak_loc, config_loc)


def get_package_list_from_file(path):
    """
    Create a list of packages to install from a provided .txt file

    Parameters
    __________
        path: Filepath to the text file (.txt) containing the list of packages to install.

    Returns
    ______
        List of filepaths to packages to install.

    Notes
    _____
        .txt file should provide the full filepath to packages to install and be newline (\n) delimited.

    """
    # Verify we have a text file
    if not path.endswith('.txt'):
        raise RuntimeError("Package List must be a newline(\n) delimited text file.")

    # read lines of the file and strip whitespace
    with open(path, 'r') as f:
        pkg_list = [line.rstrip().rstrip("/") for line in f]

    # Verify that we are not given an empty list
    if not pkg_list:
        raise RuntimeError("No packages found to be installed. "
                           "Please provide a file with a minimum of 1 package location.")

    return pkg_list


def get_package_list_from_directory(path):
    """
    Build a package list from the directories (assumed to be packages) in the provided directory.

    Parameters
    __________
        path: the full filepath to the directory storing packages to be installed.

    Returns
    _______
        List of filepaths for the packages to be installed

    Raises
    ______
        RuntimeError when the provided path does not exist or it is not a directory.
    """
    # Verify the provided parent directory exists
    if not os.path.exists(path):
        raise RuntimeError(f"Specified parent directory does not exist. {path} Not Found.")
    if not os.path.isdir(path):
        raise RuntimeError(f"Specified parent directory is not a directory. {path} is not a directory.")

    pkg_list = [path.rstrip("/") + "/" + x for x in os.listdir(path) if os.path.isdir(os.path.join(path, x)) and
                not x.startswith('.') and not x.startswith('__')]
    return pkg_list


if __name__ == "__main__":
    parser = optparse.OptionParser()
    parser.add_option("--from_file", dest="pkg_list_file", action="store_true", default=False,
                      help="Indicates that your supplied pkg_path will be a file listing the packages to be installed.")
    parser.add_option("--from_parent", dest="parent_dir", action="store_true", default=False,
                      help="Indicates that your supplied pkg_path will be a directory containing all pkgs to be installed.")
    parser.add_option("-p", "--pkg_path", dest="pkg",
                      help="Full Path to external module you would like to configure, REQUIRED")
    parser.add_option("-a", "--ak_loc", dest="arkouda",
                      help="Full Path to Arkouda installation, required when a server module provided.")
    parser.add_option("-c", "--config_loc", dest="config_location", default="~",
                      help="Indicates the directory to save the temporary configuration files to. Defaults to ~/.")
    (options, args) = parser.parse_args()

    if not options.pkg:
        print("--pkg_path/-p is REQUIRED, but was empty.")
    elif options.pkg_list_file:
        pkg_list = get_package_list_from_file(options.pkg)
        run(pkg_list, options.arkouda, options.config_location)
    elif options.parent_dir:
        pkg_list = get_package_list_from_directory(options.pkg)
        run(pkg_list, options.arkouda, options.config_location)
    else:
        run(options.pkg, options.arkouda, options.config_location)

import glob, os, os.path, sys, time
import optparse 


def get_contrib_server_modules(fn):
    mod_list = []
    with open(fn) as f:
        for line in f.readlines():
            m = line.split("#")[0].split("/")[-1].strip()
            mod_list += [m] if m else []
    return mod_list


def build_file_list(my_loc):
    path = my_loc + "/server/*.chpl"
    return glob.glob(path)
    

def run(ak_loc, my_loc):
    graph_cfg = my_loc + "/server/ServerModules.cfg"
    arkouda_cfg = ak_loc + "/ServerModules.cfg"
    if not os.path.exists(arkouda_cfg):
        raise RuntimeError(f"Could not locate Arkouda ServerModules.cfg: {arkouda_cfg}")
    if not os.path.exists(graph_cfg):
        raise RuntimeError(f"Could not locate Graph ServerModules.cfg: {graph_cfg}")

    # Get modules listed in our ServerModules.cfg to add to Arkouda's
    mod_contrib = get_contrib_server_modules(graph_cfg)

    # Get chapel files to add to Arkouda ServerModules.cfg
    c_files = build_file_list(my_loc)

    # Generate commands the user can pipe into a shell for execution.
    # 1. Make a copy of Arkouda's ServerModules.cfg so we can add to it
    tmp_cfg = f"{my_loc}/GraphServerModules.cfg.{int(time.time())}"
    print(f"cp {arkouda_cfg} {tmp_cfg}")
    
    # 2. Append our modules to Arkouda's ServerModules.cfg
    for c in mod_contrib:
        print(f"echo {c} >> {tmp_cfg}")
    
    # 3. Generate `make` command with vars
    # If this gets to long for the shell we'll need to switch to exporting our env vars
    # If it's still too long, the Arkouda team will need to make a change to the build process.
    ak_srv_user_mods = '"' + " ".join(c_files) + '"' # setup our ARKOUDA_SERVER_USER_MODULES var
    print(f"ARKOUDA_SERVER_USER_MODULES={ak_srv_user_mods} ARKOUDA_CONFIG_FILE={tmp_cfg} make -C {ak_loc}")


if __name__ == "__main__":
    # print(os.path.dirname(os.path.realpath(__file__)))
    # print(os.path.realpath(__file__))
    parser = optparse.OptionParser()
    parser.add_option("--ak", "--arkouda", dest="arkouda", help="Path to arkouda directory, REQUIRED")
    (options, args) = parser.parse_args()

    if not options.arkouda:
        print("--ak, --arkouda option is REQUIRED but was empty")
    else:
        run(options.arkouda, os.path.dirname(os.path.realpath(__file__)))


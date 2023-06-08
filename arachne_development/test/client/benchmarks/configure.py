#!/usr/bin/env python3                                                         

import time, argparse
import numpy as np
import arkouda as ak
import random
import string
import arachne_development.graph as njit

def get_config():
    cfg = ak.get_config()
    print("Number of Locales=", cfg["numLocales"])
    print("number of PUs =", cfg["numPUs"])
    print("Max Tasks =", cfg["maxTaskPar"])
    print("Memory =", cfg["physicalMemory"])
    print("Version =", cfg["arkoudaVersion"])

def create_parser():
    parser = argparse.ArgumentParser(description="Get configuration information of arkouda server.")
    parser.add_argument('hostname', help='Hostname of arkouda server')
    parser.add_argument('port', type=int, help='Port of arkouda server')
    return parser
  
if __name__ == "__main__":    
    parser = create_parser()
    args = parser.parse_args()

    print("ARKOUDA CONFIGURATION INFORMATION") 
    ak.verbose = False
    ak.connect(args.hostname, args.port) 

    get_config()

    ak.shutdown()

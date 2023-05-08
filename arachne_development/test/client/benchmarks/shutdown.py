#!/usr/bin/env python3                                                         

import time, argparse
import numpy as np
import arkouda as ak

def create_parser():
    parser = argparse.ArgumentParser(description="For shutdown the arkouda server")
    parser.add_argument('hostname', help='Hostname of arkouda server')
    parser.add_argument('port', type=int, help='Port of arkouda server')
    return parser

if __name__ == "__main__":
    import sys
    parser = create_parser()
    args = parser.parse_args()
    ak.verbose = True
    ak.connect(args.hostname, args.port)
    ak.shutdown()

from __future__ import annotations

import itertools
from typing import cast, List, Optional, Union
from typeguard import typechecked
from arkouda.client import generic_msg
from arkouda.pdarrayclass import pdarray, create_pdarray, \
    unregister_pdarray_by_name, RegistrationError
from arkouda.strings import Strings
from arkouda.logger import getArkoudaLogger
import numpy as np  # type: ignore
import json
from arkouda.infoclass import information
from arkouda.dtypes import dtype


__all__ = ["lcs"]


@typechecked
def lcs(string1: Strings,string2:Strings) -> Strings:
    """
        given two strings, return the longest common subsequence
    """
    cmd = "segmentedStrLCS"
    args ={"StrEntry1":string1.entry,"StrEntry2":string2.entry }
    repMsg = generic_msg(cmd=cmd, args=args)
    return Strings.from_return_msg(cast(str, repMsg)) 


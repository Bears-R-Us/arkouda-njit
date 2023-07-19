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
from arkouda.dtypes import resolve_scalar_dtype, translate_np_dtype, int64
import json
from arkouda.infoclass import information
from arkouda.dtypes import dtype
from arkouda.dtypes import int64 as akint64
from arkouda.pdarraysetops import in1d

__all__ = ["lcs"]


@typechecked
def lcs(string1: Strings,string2:Strings) -> Strings:
    """
        given two strings, return the longest common subsequence
    """
    cmd = "segmentedStrLCS"
    args ={"StrName1":string1,"StrName2":string2 }
    repMsg = generic_msg(cmd=cmd, args=args)
    return Strings(*(cast(str, repMsg)))


#!/bin/bash
# Shell function for launching arkouda_server on Wulver via SLURM/GASNet.
# Source this file to make chpl_wulver_executor available in your shell:
#   source /path/to/chpl_wulver_executor.sh
#
# Usage:
#   chpl_wulver_executor --filename=arkouda_server -nl 4 \
#       --partition=general --qos=standard --time=2:00:00
#
# Must be run from the directory containing the arkouda_server binary.

function chpl_wulver_executor() {
    local filename=""
    local nl=1
    local partition="general"
    local qos="standard"
    local time="24:00:00"
    local cpus=32
    local profiling=false

    while [[ $# -gt 0 ]]; do
        case "$1" in
            --filename=*) filename="${1#*=}"; shift ;;
            -nl)          nl="$2"; shift 2 ;;
            --partition=*) partition="${1#*=}"; shift ;;
            --qos=*)      qos="${1#*=}"; shift ;;
            --time=*)     time="${1#*=}"; shift ;;
            --cpus=*)     cpus="${1#*=}"; shift ;;
            --profiling)  profiling=true; shift ;;
            *) echo "Unknown option: $1"; shift ;;
        esac
    done

    if [ -z "$filename" ]; then
        echo "Error: --filename is required"
        return 1
    fi

    local cmd_output
    cmd_output=$("./$filename" -nl "$nl" --dry-run)

    local modified_cmd
    modified_cmd=$(echo "$cmd_output" | sed \
        "s/--account=${CHPL_LAUNCHER_ACCOUNT}/--account=${CHPL_LAUNCHER_ACCOUNT} --partition=$partition --qos=$qos --time=$time --cpus-per-task=$cpus/")

    echo "Executing: $modified_cmd"
    export CHPL_RT_NUM_THREADS_PER_LOCALE=$cpus
    eval "$modified_cmd --memTrack --memLeaks"
}
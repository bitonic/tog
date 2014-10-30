#!/bin/bash

# Taken from http://github.com/scvalex/script-fu

set -e

function usage {
    me=$(basename $0)
    echo "Usage: ${me} [FILE]"
    echo "  Runs 'make' when one of the files changes."
}

function snapshot_files {
    snapshot=''
    for file in $1; do
        snapshot=${snapshot}$(ls -lc --time-style=+%T:%N ${file} | cut -d' ' -f6),
    done
}

function check_snapshot {
    aux_snapshot=${snapshot}
    snapshot_files "$1"
    if [ "x${snapshot}" != "x${aux_snapshot}" ]; then
        return 0
    else
        return 1
    fi
}

# Colours and styles
txtbld=$(tput bold)             # Bold
bldred=${txtbld}$(tput setaf 1) #  Red
bldgre=${txtbld}$(tput setaf 2) #  Green
txtrst=$(tput sgr0)             # Reset

# Check for inotifywait
if ! type inotifywait > /dev/null; then
    echo "The command 'inotifywait' is required but not available."
    echo "Install 'inotify-tools'."
    exit 1
fi

# Parse command line
while getopts "h" opt; do
    case ${opt} in
        h)
            usage $0
            exit 0
            ;;
    esac
done
shift $((${OPTIND} - 1))

# Loop forever
files="$*"
snapshot_files "${files}"
while true; do
    echo "${txtbld}### Building...${txtrst}"
    if make; then
        echo -e "${bldgre}### Done${txtrst}\n"
    else
        echo -e "${bldred}### Build failed${txtrst}\n"
    fi

    if check_snapshot "${files}"; then
        echo "${txtbld}### Files changed while building${txtrst}"
        continue
    fi

    echo "${txtbld}### Waiting for filesystem changes...${txtrst}"
    inotifywait -q -r -e create -e close_write ${files}
    echo -e "${txtbld}### Files changed${txtrst}\n"
    snapshot_files "${files}"
done

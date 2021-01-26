# prepare rosette benchmarks for the purpose of testing rosette solver
import time
import os
import json
import csv
from subprocess import Popen, PIPE, STDOUT, check_output
import signal

from pprint import pprint

import sys


def run_equiv_check(rosette_file, cosette_dir, time_limit, log_file=None):
    """ Run counter example search on the given rosette file
    Args:
        rosette_file: a rosette file that provides
    """

    case_name = os.path.splitext(os.path.basename(rosette_file))[0]
    cmd_ros = f'cd {cosette_dir}; sh ./rosette_solve.sh {rosette_file} {time_limit}'

    if log_file:
        cmd_ros += " > {}".format(log_file)

    proc = Popen(cmd_ros, shell=True, stdout=PIPE, stderr=PIPE)

    result = ""
    while True:
        retcode = proc.poll()
        if retcode is not None:
            result = proc.stdout.read() + proc.stderr.read()
            break
        else:
            time.sleep(.1)
            continue

    result = [l.strip() for l in result.decode("utf-8").split("\n") if l.strip() != ""]
    result = "\n".join(result[result.index("[[testing start]] --------------------"):])
    return result

if __name__ == '__main__':
    input_files = ["rosette/oopsla-benchmarks/cex-benchmarks/CA1.rkt"]
    for infile in input_files:
        result = run_equiv_check(infile, ".", 10)

        print(result)
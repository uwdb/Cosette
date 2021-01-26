# prepare rosette benchmarks for the purpose of testing rosette solver
import time
import os
import json
import csv
from subprocess import Popen, PIPE, STDOUT, check_output
import signal

from pprint import pprint

import sys


def run_equiv_check(rosette_file, cosette_dir, log_file):

    case_name = os.path.splitext(os.path.basename(rosette_file))[0]
    cmd_ros = 'cd {}; ./rosette_solve.sh {}'.format(cosette_dir, rosette_file)

    if log_file:
        cmd_ros += " > {}".format(log_file)

    proc = Popen(cmd_ros, shell=True, stdout=PIPE, stderr=PIPE)

    while True:
        retcode = proc.poll()
        if retcode is not None:
            result = proc.stdout.read() + proc.stderr.read()
            break
        else:
            time.sleep(.1)
            continue

    return result

if __name__ == '__main__':
    input_files = ["rosette/oopsla-benchmarks/cex-benchmarks/CA4.rkt"]
    for infile in input_files:
        result = run_equiv_check(infile, ".", "__temp_fine_cex__.log")

        print(result)
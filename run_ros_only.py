# prepare rosette benchmarks for the purpose of testing rosette solver
import time
import os
import json
import csv
from subprocess import Popen, PIPE, STDOUT, check_output
import signal

from pprint import pprint

import solver
import sys

def quick_parse(input_file):
    with open(input_file, "r") as f:
        content = "\n".join(f.readlines())
        status, rosette_file = solver.gen_rosette(content, ".")
        return status, rosette_file

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
    input_files = ["duke_test_1.cos"]
    for infile in input_files:
        status, ros_file = quick_parse(infile)
        splitted = ros_file.split("\n")
        splitted[2] = '(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt")'
        ros_file = "\n".join(splitted)

        with open("__temp_find_cex__.rkt", "w") as f:
            f.write(ros_file)

        result = run_equiv_check("__temp_find_cex__.rkt", ".", "__temp_fine_cex__.log")

        print(result)
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

    raw_output = ""
    while True:
        retcode = proc.poll()
        if retcode is not None:
            raw_output = proc.stdout.read() + proc.stderr.read()
            break
        else:
            time.sleep(.1)
            continue

    raw_output = raw_output.decode("utf-8") 
    result = [l.strip() for l in raw_output.split("\n") if l.strip() != ""]
    result = result[result.index("[[testing start]] --------------------")+1:]

    if all([l.startswith("[EQ]") for l in result]):
        return json.dumps({"status": "EQ", "test_log": raw_output})
    elif result[-2].startswith("[NEQ]"):
        res = json.loads(result[-1])
        res["test_log"] = raw_output
        return json.dumps(res)
    else:
        return json.dumps({"status": "ERROR", "test_log": raw_output})
    
    #return result

if __name__ == '__main__':
    input_files = ["rosette/oopsla-benchmarks/cex-benchmarks/CA1.rkt"]
    for infile in input_files:
        result = run_equiv_check(infile, "..", 10)

        print(result)
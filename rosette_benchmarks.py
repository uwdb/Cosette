# prepare rosette benchmarks for the purpose of testing rosette solver
 
import time
import os
import json
from subprocess import Popen, PIPE, STDOUT

import solver

def prepare_calcite_benchmarks(output_dir):
    """ run calcite examples """
    folder = "./examples/calcite/"

    # get already generated rules, since some of them may be edited
    generated_rules = {}
    for filename in os.listdir(folder):
        if filename.endswith(".cos"):
            case_name = filename[:-4]
            with open(os.path.join(folder, filename), 'r') as source_file:
                cos = source_file.read()
                generated_rules[case_name] = cos

    # run all the rule from the json file
    with open(os.path.join(folder, 'calcite_tests.json')) as input_file:
        calcite_rules = json.load(input_file)

    for rule in calcite_rules:
        rname = rule["name"]

        if rname in generated_rules:
            cos = generated_rules[rname]
        else:
            cos = gen_cos_files.gen_cos_source(rule["q1"], rule["q2"])

        status, rosette_file = solver.gen_rosette(cos, ".")

        if status == True:
            with open(os.path.join(output_dir, rname + ".rkt"), "w") as out_file:
                out_file.write(rosette_file)


def prepare_cesp544hw_benchmarks(output_dir):
    pass


def run_benchmarks(input_dir, cosette_dir="."):
    for fname in os.listdir(input_dir):
        if fname.endswith('.rkt'):
            result = run_benchmark(os.path.join(input_dir, fname), cosette_dir)
            print fname
            print result
            print "======"
            sys.exit(-1)


def run_benchmark(rosette_file, cos_folder):
    cmd_ros = 'cd {}; ./rosette_solve.sh '.format(cos_folder) + rosette_file
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
    #prepare_calcite_benchmarks(output_dir=os.path.join("benchmarks", "calcite"))
    run_benchmarks("benchmarks/calcite")

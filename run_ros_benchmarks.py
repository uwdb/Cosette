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


def prepare_calcite_benchmarks(input_dir, output_dir):    
    # get already generated rules, since some of them may be edited
    generated_rules = {}
    for filename in os.listdir(input_dir):
        if filename.endswith(".cos"):
            case_name = filename[:-4]
            with open(os.path.join(input_dir, filename), 'r') as source_file:
                cos = source_file.read()
                generated_rules[case_name] = cos

    labels = {}
    with open(os.path.join(input_dir, "rosette_supported.csv")) as f:
        reader = csv.reader(f, delimiter=',')
        for row in reader:
            name = row[0]
            labels[name] = True if row[1] == "T" else False

    for fname in os.listdir(input_dir):
        case_name = fname.split(".")[0]

        if fname.endswith(".cos") and labels[case_name]:
            status, ros_file = quick_parse(os.path.join(input_dir, fname))

            if status == True:
                with open(os.path.join(output_dir, case_name + ".rkt"), "w") as out_file:
                    out_file.write(ros_file)


def prepare_hw_benchmarks(input_dir, output_dir):
    
    for filename in os.listdir(input_dir):
        if filename.endswith(".cos"):
            case_name = filename[:-4]
            with open(os.path.join(input_dir, filename), "r") as f:
                content = "\n".join(f.readlines())
                status, rosette_file = solver.gen_rosette(content, ".")

                if status == True:
                    with open(os.path.join(output_dir, case_name + ".rkt"), "w") as out_file:
                        out_file.write(rosette_file)
                else:
                    print(case_name)

'''
def run_benchmarks(input_dir, cosette_dir="."):
    def run_benchmark(rosette_file, cosette_dir):
        cmd_ros = 'cd {}; ./rosette_solve.sh '.format(cosette_dir) + rosette_file
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
    for fname in os.listdir(input_dir):
        if fname.endswith('.rkt') and (not fname.startswith("__")):
            result = run_benchmark(os.path.join(input_dir, fname), cosette_dir)
            print("[Input] Solving {}".format(fname))
            print("[Output] {}".format(result))
'''            

def run_one_benchmark(rosette_file, cosette_dir, log_dir=None):

        case_name = os.path.splitext(os.path.basename(rosette_file))[0]
        
        cmd_ros = 'cd {}; ./rosette_solve.sh {}'.format(cosette_dir, rosette_file)

        if log_dir:
            log_file = os.path.join(log_dir, case_name + ".log")
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

def run_benchmarks(input_dir, cosette_dir, log_dir):

    finished_cases = [os.path.splitext(os.path.basename(item))[0] for item in os.listdir(log_dir) 
                        if os.path.isfile(os.path.join(log_dir, item))]

    for fname in os.listdir(input_dir):
        if fname.endswith('.rkt') and not ("correct" in fname):
            if os.path.splitext(fname)[0] in finished_cases:
                print("[Ignore]{}".format(fname))
            else:
                print("[Input] Solving {}".format(fname))
                result = run_one_benchmark(os.path.join(input_dir, fname), cosette_dir, log_dir)
                #print("[Output] {}".format(result))


def parse_and_test(file_name):

    fname = sys.argv[1]

    ros_file = quick_parse(fname)
    lines = ros_file.split("\n")

    for i in range(len(lines)):
        if lines[i].startswith("(require "):
            lines[i] = '(require "../cosette.rkt" "../util.rkt" "../denotation.rkt" "../cosette.rkt" "../sql.rkt" "../evaluator.rkt" "../syntax.rkt" "../symmetry.rkt" "../test-util.rkt")'
    
    lines.append("(run-experiment ros-instance)")
    lines.append(";{}".format(fname))
    
    ros_file = "\n".join(lines)

    with open("rosette/generated/temp.rkt", "w") as f:
        f.write(ros_file)

    #run_one_benchmark("testtemp.rkt", ".", "output/temp")

if __name__ == '__main__':
    #prepare_calcite_benchmarks("./examples/calcite/", output_dir="benchmarks/calcite")
    #prepare_hw_benchmarks("./examples/homeworks/", output_dir="benchmarks/homeworks")
    #run_benchmarks("benchmarks/calcite", ".", "./output/calcite_symbreak")
    run_benchmarks("benchmarks/calcite", ".", "./output/qex_test")
    #run_benchmarks("benchmarks/homeworks", ".", "./output/homeworks_symbreak_simple")
    #print(quick_parse("temp.cos"))
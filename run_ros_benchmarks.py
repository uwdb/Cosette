# prepare rosette benchmarks for the purpose of testing rosette solver
 
import time
import os
import json
import csv
from subprocess import Popen, PIPE, STDOUT

import solver

def quick_parse(input_file):
    with open(input_file, "r") as f:
        content = "\n".join(f.readlines())
        status, rosette_file = solver.gen_rosette(content, ".")
        return rosette_file


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
    with open(os.path.join(input_dir, "calcite_labels.csv")) as f:
        reader = csv.reader(f, delimiter=',')
        for row in reader:
            name = row[0]
            labels[name] = False if row[1].lower() == "error" else True

    # run all the rule from the json file
    with open(os.path.join(input_dir, 'calcite_tests.json')) as input_file:
        calcite_rules = json.load(input_file)

    for rule in calcite_rules:
        rname = rule["name"]

        if rname in generated_rules:
            cos = generated_rules[rname]
        else:
            cos = gen_cos_files.gen_cos_source(rule["q1"], rule["q2"])

        status, rosette_file = solver.gen_rosette(cos, ".")

        if status == True:
            rname = rname if labels[rname] else ("__" + rname)
            with open(os.path.join(output_dir, rname + ".rkt"), "w") as out_file:
                out_file.write(rosette_file)


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


def run_benchmarks(input_dir, cosette_dir="."):
    for fname in os.listdir(input_dir):
        if fname.endswith('.rkt') and (not fname.startswith("__")):
            result = run_benchmark(os.path.join(input_dir, fname), cosette_dir)
            print "===="
            print fname
            print result
            

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


if __name__ == '__main__':
    #prepare_calcite_benchmarks("./examples/calcite/", output_dir="benchmarks/calcite")
    #prepare_hw_benchmarks("./examples/homeworks/", output_dir="benchmarks/homeworks")
    #run_benchmarks("benchmarks/homeworks")
    run_benchmarks("benchmarks/calcite")
    #print(quick_parse("temp.cos"))

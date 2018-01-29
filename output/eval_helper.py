import os
import sys
from pprint import pprint

def calculate_table_size(input_dir):

    case_table_size = {}

    for fname in os.listdir(input_dir):
        if fname.endswith('.rkt') and (not fname.startswith("__")):
            case_name = fname.split(".")[0][4:]
            with open(os.path.join(input_dir, fname)) as f:
                lines = [l for l in f.readlines() if "table-info" in l]
                 
                table_size = []
                for l in lines:
                    table_size.append(len(l[l.index("(list")+ 5:-4].split()))

                case_table_size[case_name] = table_size

    return case_table_size

def parse_outputs(log_dirs, table_size_dict={}):

    method_results = {}

    all_cases = []

    for log_dir in log_dirs:
        record = {}
        for fname in os.listdir(log_dir):
            case_name = fname.split(".")[0]
            all_cases.append(case_name)
            #print(case_name)
            #print(table_size_dict[case_name])
            case_result = []
            with open(os.path.join(log_dir, fname), encoding='utf-8') as f: 
                lines = [l.strip() for l in f.readlines() if "[table size]" in l]
                for l in lines:
                    table_size = l[l.index("[table size]")+len("[table size]")+2: l.index("[real time]")-2]
                    real_time = int(l[l.index("[real time]")+len("[read time]"): l.index("ms")])

                    table_size = [int(i) for i in table_size.split()]
                    case_result.append((table_size, real_time))

            record[case_name] = case_result

        method_results[log_dir] = record


    all_cases = list(set(all_cases))
    speed_up = []

    for case in all_cases:
        records = []
        record_lens = []
        for method in method_results:
            record_lens.append(len(method_results[method][case]))

        if min(record_lens) == 0:
            continue

        for method in method_results:
            records.append(method_results[method][case][min(record_lens)-1])

        v = float(records[1][1]) / records[0][1]
        if v > 1:
            print(case)
            print(v)

        speed_up.append(v)

    #print(len(speed_up))
    #print(len([x for x in speed_up if x > 1]))


if __name__ == '__main__':
    #table_size_dict = calculate_table_size(sys.argv[1])
    parse_outputs([sys.argv[1], sys.argv[2]])



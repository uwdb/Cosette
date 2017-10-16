import pandas as pd
import matplotlib.pyplot as plt

RESULT_FILE = "./examples/calcite/calcite_result_with_label.csv"

def analyze_result():
    """
    analyze calcite result
    """
    result = pd.read_csv(RESULT_FILE)
    # get frequency of results
    result_count = result['Result'].value_counts()
    print "Result summary"
    print result_count
    
    # filter out passed cases
    neq = result['Result'] == "NEQ"
    unknown = result['Result'] == "UNKNOWN"
    equiv = result['Result'] == "EQ"
    unsupported = result[~(neq|unknown|equiv)] 
    # get frequency of reasons
    print "reasons for unsupported cases"
    reason_count = unsupported['Reason'].value_counts()
    print reason_count
    
    supported_cases = result[neq|unknown|equiv]
    scount = pd.Series(data=[supported_cases.shape[0]], index=["COSETTE_OK"])
    agg_count = scount.append(reason_count)
    print agg_count
    # result_count.plot.bar()
    # plt.tight_layout()
    # plt.show()
    # agg_count.plot.bar()
    # plt.tight_layout()
    # plt.show()

if __name__ == '__main__':
    analyze_result()
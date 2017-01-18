import re
import json
import sys

import numpy as np
import matplotlib.pyplot as plt

N_OP_REGEX = re.compile('_\d+_')
QUEUE_SIZE_REGEX = re.compile('_\d+$')

def parse_n_op(d):
  return int(N_OP_REGEX.search(d).group(0)[1:-1])

def parse_queue_size(d):
  return int(QUEUE_SIZE_REGEX.search(d).group(0)[1:])

def is_pop(d):
  return d[:3] == 'Pop'

def is_push(d):
  return d[:4] == 'Push'

def main():
  if len(sys.argv) is not 2:
    print('Please enter a file as the first argument')
    return
  file_name = sys.argv[1]
  with open(file_name, 'r') as f:
    raw = f.readline().strip()
  json_raw = json.loads(raw)

  data = None
  for d in json_raw['results']:
    bench = str(d['benchName'])
    if is_pop(bench) and parse_n_op(bench) == 1 and parse_queue_size(bench) == 10:
      data = np.array([x['duration'] for x in d['measurements']])

  data = np.sort(data)
  p = [100 - 10 ** x for x in np.arange(1, -2.5, -0.5)]
  x_label = np.arange(1, 4.5, 0.5)
  dat = np.percentile(data, p)
  plt.plot(x_label, dat)
  plt.yscale('log')
  plt.show()

if __name__ == '__main__':
  main()

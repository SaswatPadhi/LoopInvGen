#!/usr/bin/env python3

import argparse
import os

from glob import iglob as glob
from pprint import pprint

def main(args):
    full_maps = []
    for file in args.stats_files:
        file_map = dict()
        for line in file.readlines()[1:]:
            field = line.split(',')
            file_map[field[0]] = {
                'pass': 1 if field[1].endswith('PASS') else 0,
                'time': int(field[3]),
                'size': int(field[4]),
            }
        full_maps.append(file_map)

    num_stats = len(full_maps)
    sum_maps = [[] for i in range(num_stats)]
    scores_list = [0 for i in range(num_stats)]

    for file in glob('%s/**/*.sl' % args.benchmarks_dir, recursive=True):
        records = []
        for i in range(num_stats):
            found = [v for k,v in full_maps[i].items() if k.endswith(file)]
            if len(found) < 1:
                records.append({'pass': 0, 'time': 0, 'size': 0})
            elif len(found) > 1:
                raise Exception('Conflicting statistics for %s.' % file)
            else:
                records.append(found[0])
        max_time_score = max([r['time'] for r in records])
        max_size_score = max([r['size'] for r in records])
        for i in range(num_stats):
            records[i]['time'] = 1 if records[i]['time'] == max_time_score and max_time_score > 0 else 0
            records[i]['size'] = 1 if records[i]['size'] == max_size_score and max_time_score > 0 else 0
        for i in range(num_stats):
            pass_score = args.pass_multiplier * records[i]['pass']
            time_score = args.time_multiplier * records[i]['time']
            size_score = args.size_multiplier * records[i]['size']
            scores_list[i] += (pass_score + time_score + size_score)
            sum_maps[i].append({
                'name': file,
                'pass': pass_score,
                'time': time_score,
                'size': size_score,
            })

    pprint(scores_list)
    #pprint(sum_maps)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Compute scores using statistics files.')
    parser.add_argument('-B', '--benchmarks-dir', required=True, type=str)
    parser.add_argument('-p', '--pass-multiplier', type=int, default=5)
    parser.add_argument('-s', '--size-multiplier', type=int, default=3)
    parser.add_argument('-t', '--time-multiplier', type=int, default=1)
    parser.add_argument('stats_files', metavar='FILE',
                        type=argparse.FileType('r'), nargs='+')

    args = parser.parse_args()
    if not os.path.isdir(args.benchmarks_dir):
        raise Exception('Benchmarks directory (%s) not found!' % args.benchmarks_dir)

    main(args)

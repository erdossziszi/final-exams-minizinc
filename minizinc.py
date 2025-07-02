# Wrapper script for running MiniZinc

import os
from pathlib import Path
import subprocess
import sys
import time


def __format_time(elapsed: int) -> str:
    if elapsed < 60:
        return f'Elapsed time: {elapsed:.2f} s'
    elif elapsed < 3600:
        mins = elapsed / 60
        return f'Elapsed time: {mins:.2f} m'
    else:
        hrs = elapsed / 3600
        return f'Elapsed time: {hrs:.2f} h'


def run_model_on_input(input_path: str, output_folder: str, model_path: str = 'model.mzn'):
    input_filename = Path(input_path).name
    filename_parts = input_filename.rsplit('.', 1)

    if filename_parts[1] != 'dzn':
        print(f'Invalid input file extension: {input_filename}', file=sys.stderr)
        return

    output_filepath = f'{output_folder}/{filename_parts[0]}.txt'

    with open(output_filepath, 'w') as f:
        start_time = time.time()

        process = subprocess.Popen(['minizinc.exe', '--solver', 'Gurobi', model_path, input_path, '--verbose'], stdout=subprocess.PIPE, text=True)

        # Read line-by-line as the process runs
        for line in process.stdout:
            print(line, end='')    # to console
            f.write(line)          # to file

        process.stdout.close()
        process.wait()

        end_time = time.time()
        elapsed = end_time - start_time
        f.write(f'% time elapsed: {__format_time(elapsed)}')


    print(f'Output saved to {output_filepath}')



if __name__ == '__main__':
    if len(sys.argv) < 3:
        print('Usage: python run_minizinc.py <input_filename> <output_directory>')
        sys.exit(1)

    input_file_path = sys.argv[1]
    output_directory = sys.argv[2]

    if not os.path.exists(output_directory):
        os.makedirs(output_directory)

    run_model_on_input(sys.argv[1], sys.argv[2])

import os
from minizinc import run_model_on_input

if __name__ == '__main__':
    input_folder_path = '<full-folder-path>'
    output_folder_path = './results'

    for filename in os.listdir(input_folder_path):
        file_path = os.path.join(input_folder_path, filename)
        if os.path.isfile(file_path):  # Ensure it's a file, not a subdirectory
            run_model_on_input(file_path, output_folder_path)

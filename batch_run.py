import os
from minizinc import run_model_on_input

TIME_LIMIT = 60 * 60  # 1 hour
FORCE_UPDATE = False


def __run_model_on_folder(input_folder_path: str, output_folder_path: str):
    for filename in os.listdir(input_folder_path):
        file_path = os.path.join(input_folder_path, filename)
        output_file_path = f'{output_folder_path}/{filename.replace(".dzn", ".txt")}'

        if os.path.isfile(file_path):  # Ensure it's a file, not a subdirectory
            if os.path.isfile(output_file_path) and not FORCE_UPDATE:
                continue

            run_model_on_input(file_path, output_folder_path, time_limit_seconds=TIME_LIMIT)


if __name__ == '__main__':
    input_root_folder_path = '<full-root-folder-path>'
    output_root_folder_path = './results'

    for folder_name in os.listdir(input_root_folder_path):
        input_path = os.path.join(input_root_folder_path, folder_name)
        output_path = os.path.join(output_root_folder_path, folder_name)

        if os.path.isdir(input_path):
            if not os.path.exists(output_path):
                os.mkdir(output_path)

            __run_model_on_folder(input_path, output_path)

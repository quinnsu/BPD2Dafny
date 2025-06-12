#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from bpmn_model import BpmnModel
import os
import sys
import json
from datetime import datetime


def create_output_directory():
    """Create output directory"""
    output_dir = "parsed_results"
    os.makedirs(output_dir, exist_ok=True)
    if os.listdir(output_dir):
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        output_dir = os.path.join("parsed_results", f"batch_{timestamp}")
        os.makedirs(output_dir, exist_ok=True)
    
    return output_dir


def parse_single_file(model_file, output_dir=None):
    print(f"Start parsing BPMN model: {model_file}")
    
    try:
        if not os.path.exists(model_file):
            models_path = os.path.join("../models", model_file)
            if os.path.exists(models_path):
                model_file = models_path
            else:
                raise FileNotFoundError(f"未找到文件: {model_file}")
        
        model = BpmnModel(model_file)
        model.print_parsed_elements()
        
        if output_dir:
            json_file = model.export_parsed_data(output_dir=output_dir)
        else:
            json_file = model.export_parsed_data()
        
        print(f"Parsing completed!")
        print(f"JSON file saved: {json_file}")
        
        return model, json_file
        
    except FileNotFoundError as e:
        print(f"Error: {e}")
        return None, None
    except Exception as e:
        print(f"Parsing failed: {e}")
        return None, None


def parse_all_files_in_models():
    models_dir = "../models"
    
    if not os.path.exists(models_dir):
        print(f"Error: {models_dir} directory not found")
        return
    
    bpmn_files = [f for f in os.listdir(models_dir) if f.endswith('.bpmn')]
    
    if not bpmn_files:
        print(f"Error: {models_dir} directory not found")
        return
    
    bpmn_files.sort()
    
    print(f"Found {len(bpmn_files)} BPMN files:")
    for i, file in enumerate(bpmn_files, 1):
        print(f"  {i:2d}. {file}")
    
    output_dir = create_output_directory()
    print(f"\nOutput directory: {output_dir}")
    
    print("\n" + "="*80)
    print("Start batch parsing...")
    print("="*80)
    
    success_count = 0
    failed_files = []
    success_files = []
    
    for i, bpmn_file in enumerate(bpmn_files, 1):
        print(f"\nProcessing [{i:2d}/{len(bpmn_files)}]: {bpmn_file}")
        print("-" * 60)
        
        model, json_file = parse_single_file(os.path.join(models_dir, bpmn_file), output_dir)
        if model:
            success_count += 1
            success_files.append((bpmn_file, json_file))
        else:
            failed_files.append(bpmn_file)
    
    # generate summary report
    create_summary_report(output_dir, len(bpmn_files), success_count, success_files, failed_files)
    
    # create index file
    create_index_file(output_dir, success_files)
    
    print("\n" + "="*80)
    print("Batch parsing completed!")
    print(f"Successfully parsed: {success_count}/{len(bpmn_files)} files")
    if failed_files:
        print(f"Failed files: {len(failed_files)} files")
        for file in failed_files:
            print(f"   - {file}")
    print(f"All results saved in: {output_dir}")
    print("="*80)


def create_summary_report(output_dir, total_files, success_count, success_files, failed_files):
    report = {
        "Summary": {
            "Parsing time": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "Total files": total_files,
            "Successfully parsed": success_count,
            "Failed files": len(failed_files),
            "Success rate": f"{(success_count/total_files)*100:.1f}%"
        },
        "Success files list": [
            {
                "Index": i,
                "BPMN file": bpmn_file,
                "JSON文件": json_file
            }
            for i, (bpmn_file, json_file) in enumerate(success_files, 1)
        ],
        "Failed files list": failed_files
    }
    
    report_file = os.path.join(output_dir, "Parsing report.json")
    with open(report_file, 'w', encoding='utf-8') as f:
        json.dump(report, f, ensure_ascii=False, indent=2)
    
    print(f"Parsing report saved: {report_file}")


def create_index_file(output_dir, success_files):
    index = {
        "Index information": {
            "Creation time": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "Total files": len(success_files),
            "Output directory": output_dir
        },
        "File index": [
            {
                "id": i,
                "bpmn_file": bpmn_file,
                "json_file": json_file,
                "json_path": os.path.join(output_dir, os.path.basename(json_file))
            }
            for i, (bpmn_file, json_file) in enumerate(success_files, 1)
        ]
    }
    
    index_file = os.path.join(output_dir, "File index.json")
    with open(index_file, 'w', encoding='utf-8') as f:
        json.dump(index, f, ensure_ascii=False, indent=2)
    
    print(f"File index saved: {index_file}")


def show_usage():
    print(" BPMN parser")
    print("="*60)
    print("Usage:")
    print("  python parser_example.py                 # parse all BPMN files in models directory")
    print("  python parser_example.py <filename>      # parse specified BPMN file")
    print("\nExample:")
    print("  python parser_example.py 01_model.bpmn")
    print("  python parser_example.py ../models/02.bpmn")
    print("\nFeatures:")
    print("  Parse BPMN XML file")
    print("  Export structured JSON file")


def main():
    print("BPMN parser")
    print("="*60)
    
    if len(sys.argv) == 1:
        parse_all_files_in_models()
    elif len(sys.argv) == 2:
        if sys.argv[1] in ['-h', '--help', 'help']:
            show_usage()
            return
        model_file = sys.argv[1]
        parse_single_file(model_file)
    else:
        print("Error: Invalid arguments")
        show_usage()


if __name__ == "__main__":
    main() 
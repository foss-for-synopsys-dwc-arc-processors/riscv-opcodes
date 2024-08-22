#!/usr/bin/env python3

from constants import *
import re
import glob
import os
import pprint
import logging
import collections
import yaml
import sys

pp = pprint.PrettyPrinter(indent=2)
logging.basicConfig(level=logging.INFO, format='%(levelname)s:: %(message)s')



def process_enc_line(line, ext):
    '''
    This function processes each line of the encoding files (rv*). As part of
    the processing, the function ensures that the encoding is legal through the
    following checks::

        - there is no over specification (same bits assigned different values)
        - there is no under specification (some bits not assigned values)
        - bit ranges are in the format hi..lo=val where hi > lo
        - value assigned is representable in the bit range
        - also checks that the mapping of arguments of an instruction exists in
          arg_lut.

    If the above checks pass, then the function returns a tuple of the name and
    a dictionary containing basic information of the instruction which includes:
        - variables: list of arguments used by the instruction whose mapping
          exists in the arg_lut dictionary
        - encoding: this contains the 32-bit encoding of the instruction where
          '-' is used to represent position of arguments and 1/0 is used to
          reprsent the static encoding of the bits
        - extension: this field contains the rv* filename from which this
          instruction was included
        - match: hex value representing the bits that need to match to detect
          this instruction
        - mask: hex value representin the bits that need to be masked to extract
          the value required for matching.
    '''
    single_dict = {}

    # fill all bits with don't care. we use '-' to represent don't care
    # TODO: hardcoded for 32-bits.
    encoding = ['-'] * 32

    # get the name of instruction by splitting based on the first space
    [name, remaining] = line.split(' ', 1)

    # replace dots with underscores as dot doesn't work with C/Sverilog, etc
    name = name.replace('.', '_')

    # remove leading whitespaces
    remaining = remaining.lstrip()

    # check each field for it's length and overlapping bits
    # ex: 1..0=5 will result in an error --> x<y
    # ex: 5..0=0 2..1=2 --> overlapping bits
    for (s2, s1, entry) in fixed_ranges.findall(remaining):
        msb = int(s2)
        lsb = int(s1)

        # check msb < lsb
        if msb < lsb:
            logging.error(
                f'{line.split(" ")[0]:<10} has position {msb} less than position {lsb} in it\'s encoding'
            )
            raise SystemExit(1)

        # illegal value assigned as per bit width
        entry_value = int(entry, 0)
        if entry_value >= (1 << (msb - lsb + 1)):
            logging.error(
                f'{line.split(" ")[0]:<10} has an illegal value {entry_value} assigned as per the bit width {msb - lsb}'
            )
            raise SystemExit(1)

        for ind in range(lsb, msb + 1):
            # overlapping bits
            if encoding[31 - ind] != '-':
                logging.error(
                    f'{line.split(" ")[0]:<10} has {ind} bit overlapping in it\'s opcodes'
                )
                raise SystemExit(1)
            bit = str((entry_value >> (ind - lsb)) & 1)
            encoding[31 - ind] = bit

    # extract bit pattern assignments of the form hi..lo=val
    remaining = fixed_ranges.sub(' ', remaining)

    # do the same as above but for <lsb>=<val> pattern. single_fixed is a regex
    # expression present in constants.py
    for (lsb, value, drop) in single_fixed.findall(remaining):
        lsb = int(lsb, 0)
        value = int(value, 0)
        if encoding[31 - lsb] != '-':
            logging.error(
                f'{line.split(" ")[0]:<10} has {lsb} bit overlapping in it\'s opcodes'
            )
            raise SystemExit(1)
        encoding[31 - lsb] = str(value)

    # convert the list of encodings into a single string for match and mask
    match = "".join(encoding).replace('-','0')
    mask = "".join(encoding).replace('0','1').replace('-','0')

    # check if all args of the instruction are present in arg_lut present in
    # constants.py
    args = single_fixed.sub(' ', remaining).split()
    encoding_args = encoding.copy()
    for a in args:
        if a not in arg_lut:
            logging.error(f' Found variable {a} in instruction {name} whose mapping in arg_lut does not exist')
            raise SystemExit(1)
        else:
            (msb, lsb) = arg_lut[a]
            for ind in range(lsb, msb + 1):
                # overlapping bits
                if encoding_args[31 - ind] != '-':
                    logging.error(f' Found variable {a} in instruction {name} overlapping {encoding_args[31 - ind]} variable in bit {ind}')
                    raise SystemExit(1)
                encoding_args[31 - ind] = a

    # update the fields of the instruction as a dict and return back along with
    # the name of the instruction
    single_dict['encoding'] = "".join(encoding)
    single_dict['variable_fields'] = args
    single_dict['extension'] = [os.path.basename(ext)]
    single_dict['match']=hex(int(match,2))
    single_dict['mask']=hex(int(mask,2))

    return (name, single_dict)

def same_base_isa(ext_name, ext_name_list):
    type1 = ext_name.split("_")[0]
    for ext_name1 in ext_name_list:
        type2 = ext_name1.split("_")[0]
        # "rv" mean insn for rv32 and rv64
        if (type1 == type2 or
            (type2 == "rv" and (type1 == "rv32" or type1 == "rv64")) or
            (type1 == "rv" and (type2 == "rv32" or type2 == "rv64"))):
            return True
    return False

def overlaps(x, y):
    x = x.rjust(len(y), '-')
    y = y.rjust(len(x), '-')

    for i in range(0, len(x)):
        if not (x[i] == '-' or y[i] == '-' or x[i] == y[i]):
            return False

    return True

def overlap_allowed(a, x, y):
    return x in a and y in a[x] or \
           y in a and x in a[y]

def extension_overlap_allowed(x, y):
    return overlap_allowed(overlapping_extensions, x, y)

def instruction_overlap_allowed(x, y):
    return overlap_allowed(overlapping_instructions, x, y)

def create_inst_dict(file_filter, include_pseudo=True, include_pseudo_ops=[]):
    '''
    This function return a dictionary containing all instructions associated
    with an extension defined by the file_filter input. The file_filter input
    needs to be rv* file name with out the 'rv' prefix i.e. '_i', '32_i', etc.

    Each node of the dictionary will correspond to an instruction which again is
    a dictionary. The dictionary contents of each instruction includes:
        - variables: list of arguments used by the instruction whose mapping
          exists in the arg_lut dictionary
        - encoding: this contains the 32-bit encoding of the instruction where
          '-' is used to represent position of arguments and 1/0 is used to
          reprsent the static encoding of the bits
        - extension: this field contains the rv* filename from which this
          instruction was included
        - match: hex value representing the bits that need to match to detect
          this instruction
        - mask: hex value representin the bits that need to be masked to extract
          the value required for matching.

    In order to build this dictionary, the function does 2 passes over the same
    rv<file_filter> file. The first pass is to extract all standard
    instructions. In this pass, all pseudo ops and imported instructions are
    skipped. For each selected line of the file, we call process_enc_line
    function to create the above mentioned dictionary contents of the
    instruction. Checks are performed in this function to ensure that the same
    instruction is not added twice to the overall dictionary.

    In the second pass, this function parses only pseudo_ops. For each pseudo_op
    this function checks if the dependent extension and instruction, both, exist
    before parsing it. The pseudo op is only added to the overall dictionary if
    the dependent instruction is not present in the dictionary, else it is
    skipped.


    '''
    opcodes_dir = os.path.dirname(os.path.realpath(__file__))
    instr_dict = {}
    pseudo_origins = {}  # New dictionary to store pseudo-instruction origins


    # file_names contains all files to be parsed in the riscv-opcodes directory
    file_names = []
    for fil in file_filter:
        file_names += glob.glob(f'{opcodes_dir}/{fil}')
    file_names.sort(reverse=True)
    # first pass if for standard/regular instructions
    logging.debug('Collecting standard instructions first')
    for f in file_names:
        logging.debug(f'Parsing File: {f} for standard instructions')
        with open(f) as fp:
            lines = (line.rstrip()
                     for line in fp)  # All lines including the blank ones
            lines = list(line for line in lines if line)  # Non-blank lines
            lines = list(
                line for line in lines
                if not line.startswith("#"))  # remove comment lines

        # go through each line of the file
        for line in lines:
            # if the an instruction needs to be imported then go to the
            # respective file and pick the line that has the instruction.
            # The variable 'line' will now point to the new line from the
            # imported file

            # ignore all lines starting with $import and $pseudo
            if '$import' in line or '$pseudo' in line:
                continue
            logging.debug(f'     Processing line: {line}')

            # call process_enc_line to get the data about the current
            # instruction
            (name, single_dict) = process_enc_line(line, f)
            ext_name = os.path.basename(f)

            # if an instruction has already been added to the filtered
            # instruction dictionary throw an error saying the given
            # instruction is already imported and raise SystemExit
            if name in instr_dict:
                var = instr_dict[name]["extension"]
                if same_base_isa(ext_name, var):
                    # disable same names on the same base ISA
                    err_msg = f'instruction : {name} from '
                    err_msg += f'{ext_name} is already '
                    err_msg += f'added from {var} in same base ISA'
                    logging.error(err_msg)
                    raise SystemExit(1)
                elif instr_dict[name]['encoding'] != single_dict['encoding']:
                    # disable same names with different encodings on different base ISAs
                    err_msg = f'instruction : {name} from '
                    err_msg += f'{ext_name} is already '
                    err_msg += f'added from {var} but each have different encodings in different base ISAs'
                    logging.error(err_msg)
                    raise SystemExit(1)
                instr_dict[name]['extension'].extend(single_dict['extension'])
            else:
              for key in instr_dict:
                  item = instr_dict[key]
                  if overlaps(item['encoding'], single_dict['encoding']) and \
                    not extension_overlap_allowed(ext_name, item['extension'][0]) and \
                    not instruction_overlap_allowed(name, key) and \
                    same_base_isa(ext_name, item['extension']):
                      # disable different names with overlapping encodings on the same base ISA
                      err_msg = f'instruction : {name} in extension '
                      err_msg += f'{ext_name} overlaps instruction {key} '
                      err_msg += f'in extension {item["extension"]}'
                      logging.error(err_msg)
                      raise SystemExit(1)

            if name not in instr_dict:
                # update the final dict with the instruction
                instr_dict[name] = single_dict

    # second pass if for pseudo instructions
    logging.debug('Collecting pseudo instructions now')
    for f in file_names:
        logging.debug(f'Parsing File: {f} for pseudo_ops')
        with open(f) as fp:
            lines = (line.rstrip()
                     for line in fp)  # All lines including the blank ones
            lines = list(line for line in lines if line)  # Non-blank lines
            lines = list(
                line for line in lines
                if not line.startswith("#"))  # remove comment lines

        # go through each line of the file
        for line in lines:

            # ignore all lines not starting with $pseudo
            if '$pseudo' not in line:
                continue
            logging.debug(f'     Processing line: {line}')

            # use the regex pseudo_regex from constants.py to find the dependent
            # extension, dependent instruction, the pseudo_op in question and
            # its encoding
            (ext, orig_inst, pseudo_inst, line) = pseudo_regex.findall(line)[0]
            ext_file = f'{opcodes_dir}/{ext}'

            # check if the file of the dependent extension exist. Throw error if
            # it doesn't
            if not os.path.exists(ext_file):
                ext1_file = f'{opcodes_dir}/unratified/{ext}'
                if not os.path.exists(ext1_file):
                    logging.error(f'Pseudo op {pseudo_inst} in {f} depends on {ext} which is not available')
                    raise SystemExit(1)
                else:
                    ext_file = ext1_file

            # check if the dependent instruction exist in the dependent
            # extension. Else throw error.
            found = False
            for oline in open(ext_file):
                if not re.findall(f'^\\s*{orig_inst}\\s+',oline):
                    continue
                else:
                    found = True
                    break
            if not found:
                logging.error(f'Orig instruction {orig_inst} not found in {ext}. Required by pseudo_op {pseudo_inst} present in {f}')
                raise SystemExit(1)


            (name, single_dict) = process_enc_line(pseudo_inst + ' ' + line, f)
            single_dict['is_pseudo'] = True  # Mark as pseudo-instruction
            single_dict['orig_inst'] = orig_inst.replace('.', '_')  # Store originating instruction

            # add the pseudo_op to the dictionary only if the original
            # instruction is not already in the dictionary.
            if orig_inst.replace('.','_') not in instr_dict \
                    or include_pseudo \
                    or name in include_pseudo_ops:

                # update the final dict with the instruction
                if name not in instr_dict:
                    instr_dict[name] = single_dict
                    logging.debug(f'        including pseudo_ops:{name}')
                else:
                    # if a pseudo instruction has already been added to the filtered
                    # instruction dictionary but the extension is not in the current
                    # list, add it
                    ext_name = single_dict['extension']
                    if ext_name not in instr_dict[name]['extension']:
                        instr_dict[name]['extension'].extend(ext_name)

                # Store the pseudo-instruction origin
                pseudo_origins[name] = orig_inst.replace('.', '_')

            else:
                logging.debug(f'        Skipping pseudo_op {pseudo_inst} since original instruction {orig_inst} already selected in list')

    # Update original instructions with their pseudo-instructions
    for pseudo, orig in pseudo_origins.items():
        if orig in instr_dict:
            if 'pseudo_ops' not in instr_dict[orig]:
                instr_dict[orig]['pseudo_ops'] = []
            instr_dict[orig]['pseudo_ops'].append(pseudo)

    # third pass if for imported instructions
    logging.debug('Collecting imported instructions')
    for f in file_names:
        logging.debug(f'Parsing File: {f} for imported ops')
        with open(f) as fp:
            lines = (line.rstrip()
                     for line in fp)  # All lines including the blank ones
            lines = list(line for line in lines if line)  # Non-blank lines
            lines = list(
                line for line in lines
                if not line.startswith("#"))  # remove comment lines

        # go through each line of the file
        for line in lines:
            # if the an instruction needs to be imported then go to the
            # respective file and pick the line that has the instruction.
            # The variable 'line' will now point to the new line from the
            # imported file

            # ignore all lines starting with $import and $pseudo
            if '$import' not in line :
                continue
            logging.debug(f'     Processing line: {line}')

            (import_ext, reg_instr) = imported_regex.findall(line)[0]
            import_ext_file = f'{opcodes_dir}/{import_ext}'

            # check if the file of the dependent extension exist. Throw error if
            # it doesn't
            if not os.path.exists(import_ext_file):
                ext1_file = f'{opcodes_dir}/unratified/{import_ext}'
                if not os.path.exists(ext1_file):
                    logging.error(f'Instruction {reg_instr} in {f} cannot be imported from {import_ext}')
                    raise SystemExit(1)
                else:
                    ext_file = ext1_file
            else:
                ext_file = import_ext_file

            # check if the dependent instruction exist in the dependent
            # extension. Else throw error.
            found = False
            for oline in open(ext_file):
                if not re.findall(f'^\\s*{reg_instr}\\s+',oline):
                    continue
                else:
                    found = True
                    break
            if not found:
                logging.error(f'imported instruction {reg_instr} not found in {ext_file}. Required by {line} present in {f}')
                logging.error(f'Note: you cannot import pseudo/imported ops.')
                raise SystemExit(1)

            # call process_enc_line to get the data about the current
            # instruction
            (name, single_dict) = process_enc_line(oline, f)

            # if an instruction has already been added to the filtered
            # instruction dictionary throw an error saying the given
            # instruction is already imported and raise SystemExit
            if name in instr_dict:
                var = instr_dict[name]["extension"]
                if instr_dict[name]['encoding'] != single_dict['encoding']:
                    err_msg = f'imported instruction : {name} in '
                    err_msg += f'{os.path.basename(f)} is already '
                    err_msg += f'added from {var} but each have different encodings for the same instruction'
                    logging.error(err_msg)
                    raise SystemExit(1)
                instr_dict[name]['extension'].extend(single_dict['extension'])
            else:
                # update the final dict with the instruction
                instr_dict[name] = single_dict
    return instr_dict

def make_asciidoc_instructions(instr_dict):
    extension_content = {}
    instruction_list = []

    for instr_name, instr_data in instr_dict.items():
        # Generate a unique anchor for this instruction
        anchor = f'[[instruction-{instr_name.lower().replace(".", "-")}]]'

        # Generate the content for this instruction
        instr_content = f'{anchor}\n'
        instr_content += f'=== {instr_name.upper()}\n\n'
        instr_content += make_asciidoc_synopsis(instr_name)
        instr_content += make_asciidoc_mnemonic(instr_name, instr_data)
        instr_content += make_asciidoc_encoding(instr_name, instr_data)
        instr_content += make_asciidoc_description(instr_name)
        instr_content += make_asciidoc_argument_table(instr_name, instr_data)
        instr_content += make_asciidoc_sail(instr_name)
        instr_content += f'Included in:: {asciidoc_extension_info(instr_data["extension"])}\n\n'
        
        instr_content += '<<<\n\n'

        # Add the content to the appropriate extension
        for ext in instr_data['extension']:
            if ext not in extension_content:
                extension_content[ext] = ''
            extension_content[ext] += instr_content

        # Add to instruction list for the reference table
        instruction_list.append((instr_name, instr_data))

    return extension_content, instruction_list


def make_asciidoc_synopsis(instr_name):
    """
    Search for the synopsis of a given instruction in a file named "synopsis".

    Args:
    instr_name (str): The name of the instruction to search for

    Returns:
    str: AsciiDoc formatted string containing the synopsis of the instruction
    """
    asciidoc_content = 'Synopsis:: '

    # Get the directory of the current script
    current_dir = os.path.dirname(os.path.realpath(__file__))

    # Path to the synopsis file
    synopsis_file = os.path.join(current_dir, "synopsis")

    if os.path.exists(synopsis_file):
        with open(synopsis_file, 'r') as f:
            lines = f.readlines()
            for line in lines:
                parts = line.strip().split(' ', 1)
                if len(parts) == 2 and parts[0].lower() == instr_name.lower():
                    asciidoc_content += parts[1] + '\n\n'
                    return asciidoc_content

    # If no synopsis is found, return a default message
    asciidoc_content += 'No synopsis available.\n\n'
    return asciidoc_content


def make_asciidoc_reference_table(instruction_list):
    table_content = "== Instruction Reference Table\n\n"
    table_content += "[cols=\"2,4\", options=\"header\"]\n"
    table_content += "|===\n"
    table_content += "|Instruction |Synopsis\n\n"
    for instr_name, instr_data in sorted(instruction_list, key=lambda x: x[0]):
        anchor = f"instruction-{instr_name.lower().replace('.', '-')}"
        synopsis = make_asciidoc_synopsis(instr_name).strip()
        table_content += f"|<<{anchor},{instr_name.upper()}>> |{synopsis}\n\n"
    table_content += "|===\n\n"
    return table_content
    

def make_asciidoc_encoding(instr_name, instr_data):
    '''
    Generates AsciiDoc content for instruction encodings with comments.
    
    Args:
    instr_name (str): The name of the instruction
    instr_data (dict): A dictionary containing instruction data

    Returns:
    str: AsciiDoc formatted string with instruction encoding information
    '''
    asciidoc_content = 'Encoding::\n'
    asciidoc_content += '[wavedrom, , svg]\n'
    asciidoc_content += '....\n'
    asciidoc_content += '{reg: [\n'
    
    encoding = instr_data['encoding']
    var_fields = instr_data.get('variable_fields', [])
    
    # Create a list of tuples (start_bit, end_bit, field_name)
    fields = []
    for field_name in var_fields:
        if field_name in arg_lut:
            start_bit, end_bit = arg_lut[field_name]
            fields.append((start_bit, end_bit, field_name))
    
    # Sort fields by start_bit in descending order
    fields.sort(key=lambda x: x[0], reverse=True)
    
    instruction_type = determine_instruction_type(fields)
    print (instr_name, instruction_type)


    bits = []
    current_bit = 31

    for start_bit, end_bit, field_name in fields:
        # Add any fixed bits before this field
        if current_bit > start_bit:
            fixed_bits = encoding[31-current_bit:31-start_bit]
            print (fixed_bits)
            print (current_bit, start_bit)
            if fixed_bits:
                # Check for funct3 (3 bits, typically at 14-12)
                if end_bit - start_bit == 3 and current_bit == 14:
                    hex_value = hex(int(fixed_bits, 2))
                    bits.append(f'{{bits: {current_bit-start_bit}, name: {hex_value}, attr:["funct3"]}}')
                     # Check for funct7 (7 bits at the start, only in R-type instructions)
                elif current_bit - start_bit == 7 and current_bit == 31 and instruction_type in [INSTR_TYPE_R, INSTR_TYPE_R]:
                    hex_value = hex(int(fixed_bits, 2))
                    bits.append(f'{{bits: {current_bit-start_bit}, name: {hex_value}, attr:["funct7"]}}')
                else:
                    hex_value = hex(int(fixed_bits, 2))
                    bits.append(f'{{bits: {current_bit-start_bit}, name: {hex_value}, attr:["funct3"]}}')

                
        # Add the variable field
        field_name = asciidoc_mapping.get(field_name, field_name)
        if 'imm' in field_name and '[' in field_name and ']' in field_name:
            # Handle immediate fields
            parts = field_name.split('[')[1].split(']')[0].split('|')
            total_bits = start_bit - end_bit + 1
            bits_used = 0
            for part in parts:
                if ':' in part:
                    start, end = map(int, part.split(':'))
                    part_bits = start - end + 1
                    bits.append(f'{{bits: {part_bits}, name: \'imm[{part}]\'}}')
                else:
                    bits.append(f'{{bits: 1, name: \'[{part}]\'}}')
                    part_bits = 1
                bits_used += part_bits
            if bits_used != total_bits:
                print(f"Warning: Mismatch in bits for {field_name} in {instr_name}")        
        else:
            bits.append(f'{{bits: {start_bit-end_bit+1}, name: \'{field_name}\'}}')

        current_bit = end_bit - 1


    
    # Add any remaining fixed bits at the end
    if current_bit >= 0:
        fixed_bits = encoding[31-current_bit:]
        if fixed_bits:
            hex_value = hex(int(fixed_bits, 2))
            bits.append(f'{{bits: {current_bit+1}, name: {hex_value}, attr: ["OP"]}}')
    
    asciidoc_content += ',\n'.join(reversed(bits))
    asciidoc_content += '\n]}\n'
    asciidoc_content += '....\n\n'
    
    return asciidoc_content

def determine_instruction_type(fields):
    """
    Determine the RISC-V instruction type based on the given fields, including specific immediate formats.
    
    :param fields: List of tuples (start_bit, end_bit, field_name)
    :return: Instruction type (R-Type, I-Type, S-Type, B-Type, U-Type, J-Type, I-immediate, S-immediate, B-immediate, U-immediate, J-immediate, or Unknown)
    """
    field_dict = {(start, end): name for start, end, name in fields}
    field_names = set(field_dict.values())
    
    # Check for specific immediate formats first
    if (31, 20) in field_dict and field_dict[(31, 20)] == 'imm12':
        return INSTR_TYPE_I_IMMEDIATE
    
    if (31, 25) in field_dict and (11, 7) in field_dict and \
       field_dict[(31, 25)] == 'imm12hi' and field_dict[(11, 7)] == 'imm12lo':
        return INSTR_TYPE_S_IMMEDIATE
    
    if (31, 31) in field_dict and (7, 7) in field_dict and (30, 25) in field_dict and (11, 8) in field_dict and \
       all(field_dict[f].startswith('bimm') for f in [(31, 31), (7, 7), (30, 25), (11, 8)]):
        return INSTR_TYPE_B_IMMEDIATE
    
    if (31, 12) in field_dict and field_dict[(31, 12)] == 'imm20':
        return INSTR_TYPE_U_IMMEDIATE
    
    if (31, 31) in field_dict and (19, 12) in field_dict and (20, 20) in field_dict and (30, 21) in field_dict and \
       all(field_dict[f].startswith('jimm') for f in [(31, 31), (19, 12), (20, 20), (30, 21)]):
        return INSTR_TYPE_J_IMMEDIATE
    
    # If not a specific immediate format, check for general instruction types
    if 'rs1' in field_names and 'rs2' in field_names and 'rd' in field_names:
        return INSTR_TYPE_R
    
    if 'rs1' in field_names and 'rd' in field_names and 'rs2' not in field_names and any('imm' in name for name in field_names):
        return INSTR_TYPE_I
    
    if 'rs1' in field_names and 'rs2' in field_names and 'rd' not in field_names and any('imm' in name for name in field_names):
        return INSTR_TYPE_S
    
    if 'rs1' in field_names and 'rs2' in field_names and 'rd' not in field_names and 'bimm12hi' in field_names and 'bimm12lo' in field_names:
        return INSTR_TYPE_B
    
    if 'rd' in field_names and 'imm20' in field_names:
        return INSTR_TYPE_U
    
    if 'rd' in field_names and 'jimm20' in field_names:
        return INSTR_TYPE_J
    
    return INSTR_TYPE_UNKNOWN

def make_asciidoc_description(instr_name):
    """
    Search for the description of a given instruction in files named "base_name"_desc.

    Args:
    instr_name (str): The name of the instruction to search for

    Returns:
    str: AsciiDoc formatted string containing the description of the instruction
    """
    asciidoc_content = 'Description:: '
    
    # Get the directory of the current script
    current_dir = os.path.dirname(os.path.realpath(__file__))
    
    # List all files in the current directory that end with '_desc'
    desc_file = os.path.join(current_dir, "description")

    with open(desc_file, 'r') as f:
        lines = f.readlines()
        # Skip the first line as it's the header
        for line in lines[1:]:
            parts = line.strip().split(' ', 1)
            if len(parts) == 2 and parts[0].lower() == instr_name.lower():
                asciidoc_content += parts[1] + '\n\n'
                return asciidoc_content
    
    # If no description is found, return a default message
    asciidoc_content += 'No description available.\n\n'
    return asciidoc_content

def make_asciidoc_argument_table(instr_name, instr_data):
    '''
    Generate an AsciiDoc table for instruction arguments.

    This function creates an AsciiDoc formatted table that lists the arguments
    of a given instruction, their direction (input/output), and their definition.

    Args:
    instr_name (str): The name of the instruction
    instr_data (dict): A dictionary containing instruction data

    Returns:
    str: AsciiDoc formatted string containing the argument table

    The function does the following:
    1. Initializes the AsciiDoc content with table headers
    2. Retrieves the variable fields (arguments) for the instruction
    3. For each field that exists in the instruction_arguments dictionary:
       - Adds a row to the table with the field name, direction, and definition
    4. Closes the table

    Note: This function assumes the existence of an 'instruction_arguments' 
    dictionary that contains information about each possible argument.
    '''
    asciidoc_content = ''
    asciidoc_content += 'Arguments::\n'
    asciidoc_content += '[%autowidth]\n'
    asciidoc_content += '[%header,cols="4,2,2"]\n'
    asciidoc_content += '|===\n'
    asciidoc_content += '|Register |Direction |Definition\n'

    # Get the variable fields (arguments) for this instruction
    var_fields = instr_data.get('variable_fields', [])

    # For each field, if it exists in the instruction_arguments dictionary,
    # add it to the table
    for field in var_fields:
        if field in instruction_arguments:
            arg_info = instruction_arguments[field]
            asciidoc_content += f"|{field} |{arg_info['direction']} |{arg_info['definition']}\n"
    
    # Close the table
    asciidoc_content += '|===\n\n'
    
    return asciidoc_content

def make_asciidoc_mnemonic(instr_name, instr_data):
    '''
    Generate an AsciiDoc formatted mnemonic representation for an instruction.

    Args:
    instr_name (str): The name of the instruction
    instr_data (dict): A dictionary containing instruction data

    Returns:
    str: AsciiDoc formatted string containing the mnemonic representation
    '''
    asciidoc_content = f'Mnemonic::\n'

    # Get the variable fields (arguments) for this instruction
    var_fields = instr_data.get('variable_fields', [])

    # Construct the mnemonic
    mnemonic = instr_name.lower()
    reg_args = []
    imm_args = []

    # Process fields
    for field in var_fields:
        mapped_field = asciidoc_mapping.get(field, field)
        if field.startswith(('imm', 'bimm')):
            imm_args.append(mapped_field)
        else:
            reg_args.append(mapped_field)

    # Combine immediate fields
    combined_imm = combine_imm_fields(imm_args)

    # Combine all arguments, registers first then immediates
    all_args = reg_args + ([combined_imm] if combined_imm else [])

    # Add the arguments to the mnemonic
    if all_args:
        mnemonic += ' ' + ', '.join(all_args)

    # Format the mnemonic in AsciiDoc
    asciidoc_content += f'+\n'
    asciidoc_content += f'`{mnemonic}`\n'
    asciidoc_content += f'+\n\n'

    return asciidoc_content

def combine_imm_fields(imm_fields):
    '''
    Combine multiple immediate fields into a single representation.

    Args:
    imm_fields (list): List of immediate field strings

    Returns:
    str: Combined immediate field representation
    '''
    if not imm_fields:
        return ''
    
    all_bits = set()
    for field in imm_fields:
        if '[' in field and ']' in field:
            range_str = field.split('[')[1].split(']')[0]
            parts = range_str.split('|')
            for part in parts:
                if ':' in part:
                    start, end = map(int, part.split(':'))
                    all_bits.update(range(min(start, end), max(start, end) + 1))
                else:
                    all_bits.add(int(part))
        elif field == 'imm':
            return 'imm'  # If there's a generic 'imm', just return it
    
    if all_bits:
        min_bit, max_bit = min(all_bits), max(all_bits)
        return f'imm[{max_bit}:{min_bit}]'
    else:
        return 'imm'    
def process_asciidoc_block(block, instr_name):
    '''
    Process a block of code for a specific instruction.
    
    This function takes a code block and an instruction name, then creates a new block
    specific to that instruction. It handles the "match op" (switch) structure,
    extracts the relevant parts, and formats them appropriately.
    
    Args:
    block (str): The original code block to process.
    instr_name (str): The name of the instruction to focus on.
    
    Returns:
    str: A new code block formatted for the specific instruction.
    '''
    
    new_block = []
    start_word = "match op"
    stop_word = "};"
    first_two_words = ""
    instr_upper = instr_name.upper()
    instr_pattern = f"RISCV_{instr_upper}"
    
    # Split the block into lines and replace the generic TYPE with the specific instruction
    block_lines = block.split('\n')
    block_lines[0] = re.sub(r'\b\w*TYPE\w*\b', instr_pattern, block_lines[0])
    
    if ", op" in block_lines[0]:
        block_lines[0] = block_lines[0].replace(", op", "")
        
    # Find the start of the "match op" (switch) block
    start_block_index = -1
    for i, line in enumerate(block_lines):
        if start_word in line:
            start_block_index = i
            first_two_words = ' '.join(line.split()[:2])
            break
        else:
            new_block.append(line)
    
    # Find the end of the "match op" (switch) block
    end_block_index = -1
    for i, line in enumerate(block_lines):
        if stop_word in line:
            end_block_index = i
            break
    
    if (start_block_index != -1) and (end_block_index != -1):
        # Process the "match op" block
        block_match_op = block_lines[start_block_index:end_block_index]
        encontrado = False
        for line in block_match_op:
            if instr_pattern in line:
                encontrado = True
            if encontrado:
                if re.search(r'\bRISCV_\w+\b', line) and instr_pattern not in line:
                    break
                elif instr_pattern in line:
                    # Format the line for the specific instruction
                    partes = line.split('=')
                    partes[0] = first_two_words.strip()
                    line = '='.join(partes).strip()
                    line = line.replace("=>", " =")
                    new_block.append('  ' + line)
                else:
                    new_block.append(line)
        
        for line in block_lines[end_block_index + 1:]:
            new_block.append(line)
    
    # Join the processed lines into a single string
    formatted_block = '\n'.join(new_block)
    return formatted_block

def find_matching_brace(text, start):
    count = 0
    for i, char in enumerate(text[start:], start):
        if char == '{':
            count += 1
        elif char == '}':
            count -= 1
            if count == 0:
                return i
    return -1

def make_asciidoc_sail(instr_name):
    file_path = "../sail-riscv/model/riscv_insts_base.sail"
    asciidoc_content = ""
    riscv_name = "RISCV_" + instr_name.upper()

    with open(file_path, 'r') as f:
        content = f.read()
        
        function_starts = list(re.finditer(r'function clause execute', content))
        
        for match in function_starts:
            start = match.start()
            end = find_matching_brace(content, start)
            if end != -1:
                block = content[start:end+1]

                if re.search(r'\b(' + re.escape(riscv_name) + r'|' + re.escape(instr_name.upper()) + r')\b', block):
                    asciidoc_content += f"Sail Code:: \n\n"
                    asciidoc_content += "[source,sail]\n"
                    asciidoc_content += "--\n"
                    asciidoc_content += process_asciidoc_block(block, instr_name)
                    asciidoc_content += "\n--\n\n"
                    return asciidoc_content  # Return the AsciiDoc formatted string

    if not asciidoc_content:
        #print(f"{instr_name} NOT found")
        asciidoc_content += f"Sail Code :: \n\n"
        asciidoc_content += f"Instruction {instr_name} sail code not found in the expected format.\n\n"
    
    return asciidoc_content

def asciidoc_extension_info(extensions):
    formatted_extensions = set()
    for ext in extensions:
        if 'rv32_' in ext:
            base = '<<rv32,RV32>>'
            clean_ext = ext.replace('rv32_', '').upper()
            formatted_ext = f"{base}{clean_ext}"
            if clean_ext == 'I':
                formatted_ext += ", RV64I"
        elif 'rv64_' in ext:
            base = 'RV64'
            clean_ext = ext.replace('rv64_', '').upper()
            formatted_ext = f"{base}{clean_ext}"
        else:
            base = '<<rv32,RV32>>, RV64'
            clean_ext = ext.replace('rv_', '').upper()
            formatted_ext = f"{base}{clean_ext}"
        
        formatted_extensions.add(formatted_ext)

    return ', '.join(sorted(formatted_extensions))

def make_priv_latex_table():
    latex_file = open('priv-instr-table.tex','w')
    type_list = ['R-type','I-type']
    system_instr = ['_h','_s','_system','_svinval', '64_h']
    dataset_list = [ (system_instr, 'Trap-Return Instructions',['sret','mret'], False) ]
    dataset_list.append((system_instr, 'Interrupt-Management Instructions',['wfi'], False))
    dataset_list.append((system_instr, 'Supervisor Memory-Management Instructions',['sfence_vma'], False))
    dataset_list.append((system_instr, 'Hypervisor Memory-Management Instructions',['hfence_vvma', 'hfence_gvma'], False))
    dataset_list.append((system_instr, 'Hypervisor Virtual-Machine Load and Store Instructions',
        ['hlv_b','hlv_bu', 'hlv_h','hlv_hu', 'hlv_w', 'hlvx_hu', 'hlvx_wu', 'hsv_b', 'hsv_h','hsv_w'], False))
    dataset_list.append((system_instr, 'Hypervisor Virtual-Machine Load and Store Instructions, RV64 only', ['hlv_wu','hlv_d','hsv_d'], False))
    dataset_list.append((system_instr, 'Svinval Memory-Management Instructions', ['sinval_vma', 'sfence_w_inval','sfence_inval_ir', 'hinval_vvma','hinval_gvma'], False))
    caption = '\\caption{RISC-V Privileged Instructions}'
    make_ext_latex_table(type_list, dataset_list, latex_file, 32, caption)

    latex_file.close()

def make_latex_table():
    '''
    This function is mean to create the instr-table.tex that is meant to be used
    by the riscv-isa-manual. This function basically creates a single latext
    file of multiple tables with each table limited to a single page. Only the
    last table is assigned a latex-caption.

    For each table we assign a type-list which capture the different instruction
    types (R, I, B, etc) that will be required for the table. Then we select the
    list of extensions ('_i, '32_i', etc) whose instructions are required to
    populate the table. For each extension or collection of extension we can
    assign Title, such that in the end they appear as subheadings within
    the table (note these are inlined headings and not captions of the table).

    All of the above information is collected/created and sent to
    make_ext_latex_table function to dump out the latex contents into a file.

    The last table only has to be given a caption - as per the policy of the
    riscv-isa-manual.
    '''
    # open the file and use it as a pointer for all further dumps
    latex_file = open('instr-table.tex','w')

    # create the rv32i table first. Here we set the caption to empty. We use the
    # files rv_i and rv32_i to capture instructions relevant for rv32i
    # configuration. The dataset is a list of 4-element tuples :
    # (list_of_extensions, title, list_of_instructions, include_pseudo_ops). If list_of_instructions
    # is empty then it indicates that all instructions of the all the extensions
    # in list_of_extensions need to be dumped. If not empty, then only the
    # instructions listed in list_of_instructions will be dumped into latex.
    caption = ''
    type_list = ['R-type','I-type','S-type','B-type','U-type','J-type']
    dataset_list = [(['_i','32_i'], 'RV32I Base Instruction Set', [], False)]
    dataset_list.append((['_i'], '', ['fence_tso','pause'], True))
    make_ext_latex_table(type_list, dataset_list, latex_file, 32, caption)

    type_list = ['R-type','I-type','S-type']
    dataset_list = [(['64_i'], 'RV64I Base Instruction Set (in addition to RV32I)', [], False)]
    dataset_list.append((['_zifencei'], 'RV32/RV64 Zifencei Standard Extension', [], False))
    dataset_list.append((['_zicsr'], 'RV32/RV64 Zicsr Standard Extension', [], False))
    dataset_list.append((['_m','32_m'], 'RV32M Standard Extension', [], False))
    dataset_list.append((['64_m'],'RV64M Standard Extension (in addition to RV32M)', [], False))
    make_ext_latex_table(type_list, dataset_list, latex_file, 32, caption)

    type_list = ['R-type']
    dataset_list = [(['_a'],'RV32A Standard Extension', [], False)]
    dataset_list.append((['64_a'],'RV64A Standard Extension (in addition to RV32A)', [], False))
    make_ext_latex_table(type_list, dataset_list, latex_file, 32, caption)

    type_list = ['R-type','R4-type','I-type','S-type']
    dataset_list = [(['_f'],'RV32F Standard Extension', [], False)]
    dataset_list.append((['64_f'],'RV64F Standard Extension (in addition to RV32F)', [], False))
    make_ext_latex_table(type_list, dataset_list, latex_file, 32, caption)

    type_list = ['R-type','R4-type','I-type','S-type']
    dataset_list = [(['_d'],'RV32D Standard Extension', [], False)]
    dataset_list.append((['64_d'],'RV64D Standard Extension (in addition to RV32D)', [], False))
    make_ext_latex_table(type_list, dataset_list, latex_file, 32, caption)

    type_list = ['R-type','R4-type','I-type','S-type']
    dataset_list = [(['_q'],'RV32Q Standard Extension', [], False)]
    dataset_list.append((['64_q'],'RV64Q Standard Extension (in addition to RV32Q)', [], False))
    make_ext_latex_table(type_list, dataset_list, latex_file, 32, caption)

    caption = '\\caption{Instruction listing for RISC-V}'
    type_list = ['R-type','R4-type','I-type','S-type']
    dataset_list = [(['_zfh', '_d_zfh','_q_zfh'],'RV32Zfh Standard Extension', [], False)]
    dataset_list.append((['64_zfh'],'RV64Zfh Standard Extension (in addition to RV32Zfh)', [], False))
    make_ext_latex_table(type_list, dataset_list, latex_file, 32, caption)

    ## The following is demo to show that Compressed instructions can also be
    # dumped in the same manner as above

    #type_list = ['']
    #dataset_list = [(['_c', '32_c', '32_c_f','_c_d'],'RV32C Standard Extension', [])]
    #dataset_list.append((['64_c'],'RV64C Standard Extension (in addition to RV32C)', []))
    #make_ext_latex_table(type_list, dataset_list, latex_file, 16, caption)

    latex_file.close()

def make_ext_latex_table(type_list, dataset, latex_file, ilen, caption):
    '''
    For a given collection of extensions this function dumps out a complete
    latex table which includes the encodings of the instructions.

    The ilen input indicates the length of the instruction for which the table
    is created.

    The caption input is used to create the latex-table caption.

    The type_list input is a list of instruction types (R, I, B, etc) that are
    treated as header for each table. Each table will have its own requirements
    and type_list must include all the instruction-types that the table needs.
    Note, all elements of this list must be present in the latex_inst_type
    dictionary defined in constants.py

    The latex_file is a file pointer to which the latex-table will dumped into

    The dataset is a list of 3-element tuples containing:
        (list_of_extensions, title, list_of_instructions)
    The list_of_extensions must contain all the set of extensions whose
    instructions must be populated under a given title. If list_of_instructions
    is not empty, then only those instructions mentioned in list_of_instructions
    present in the extension will be dumped into the latex-table, other
    instructions will be ignored.

    Once the above inputs are received then function first creates table entries
    for the instruction types. To simplify things, we maintain a dictionary
    called latex_inst_type in constants.py which is created in the same way the
    instruction dictionary is created. This allows us to re-use the same logic
    to create the instruction types table as well

    Once the header is created, we then parse through every entry in the
    dataset. For each list dataset entry we use the create_inst_dict function to
    create an exhaustive list of instructions associated with the respective
    collection of the extension of that dataset. Then we apply the instruction
    filter, if any, indicated by the list_of_instructions of that dataset.
    Thereon, for each instruction we create a latex table entry.

    Latex table specification for ilen sized instructions:
        Each table is created with ilen+1 columns - ilen columns for each bit of the
        instruction and one column to hold the name of the instruction.

        For each argument of an instruction we use the arg_lut from constants.py
        to identify its position in the encoding, and thus create a multicolumn
        entry with the name of the argument as the data. For hardcoded bits, we
        do the same where we capture a string of continuous 1s and 0s, identify
        the position and assign the same string as the data of the
        multicolumn entry in the table.

    '''
    column_size = "".join(['p{0.002in}']*(ilen+1))

    type_entries = '''
    \\multicolumn{3}{l}{31} &
    \\multicolumn{2}{r}{27} &
    \\multicolumn{1}{c}{26} &
    \\multicolumn{1}{r}{25} &
    \\multicolumn{3}{l}{24} &
    \\multicolumn{2}{r}{20} &
    \\multicolumn{3}{l}{19} &
    \\multicolumn{2}{r}{15} &
    \\multicolumn{2}{l}{14} &
    \\multicolumn{1}{r}{12} &
    \\multicolumn{4}{l}{11} &
    \\multicolumn{1}{r}{7} &
    \\multicolumn{6}{l}{6} &
    \\multicolumn{1}{r}{0} \\\\
    \\cline{2-33}\n&\n\n
''' if ilen == 32 else '''
    \\multicolumn{1}{c}{15} &
    \\multicolumn{1}{c}{14} &
    \\multicolumn{1}{c}{13} &
    \\multicolumn{1}{c}{12} &
    \\multicolumn{1}{c}{11} &
    \\multicolumn{1}{c}{10} &
    \\multicolumn{1}{c}{9} &
    \\multicolumn{1}{c}{8} &
    \\multicolumn{1}{c}{7} &
    \\multicolumn{1}{c}{6} &
    \\multicolumn{1}{c}{5} &
    \\multicolumn{1}{c}{4} &
    \\multicolumn{1}{c}{3} &
    \\multicolumn{1}{c}{2} &
    \\multicolumn{1}{c}{1} &
    \\multicolumn{1}{c}{0} \\\\
    \\cline{2-17}\n&\n\n
'''

    # depending on the type_list input we create a subset dictionary of
    # latex_inst_type dictionary present in constants.py
    type_dict = {key: value for key, value in latex_inst_type.items() if key in type_list}

    # iterate ovr each instruction type and create a table entry
    for t in type_dict:
        fields = []

        # first capture all "arguments" of the type (funct3, funct7, rd, etc)
        # and capture their positions using arg_lut.
        for f in type_dict[t]['variable_fields']:
            (msb, lsb) = arg_lut[f]
            name = f if f not in latex_mapping else latex_mapping[f]
            fields.append((msb, lsb, name))

        # iterate through the 32 bits, starting from the msb, and assign
        # argument names to the relevant portions of the instructions. This
        # information is stored as a 3-element tuple containing the msb, lsb
        # position of the arugment and the name of the argument.
        msb = ilen - 1
        y = ''
        for r in range(0,ilen):
            if y != '':
                fields.append((msb,ilen-1-r+1,y))
                y = ''
            msb = ilen-1-r-1
            if r == 31:
                if y != '':
                    fields.append((msb, 0, y))
                y = ''

        # sort the arguments in decreasing order of msb position
        fields.sort(key=lambda y: y[0], reverse=True)

        # for each argument/string of 1s or 0s, create a multicolumn latex table
        # entry
        entry = ''
        for r in range(len(fields)):
            (msb, lsb, name) = fields[r]
            if r == len(fields)-1:
                entry += f'\\multicolumn{{{msb - lsb + 1}}}{{|c|}}{{{name}}} & {t} \\\\\n'
            elif r == 0:
                entry += f'\\multicolumn{{{msb - lsb + 1}}}{{|c|}}{{{name}}} &\n'
            else:
                entry += f'\\multicolumn{{{msb - lsb + 1}}}{{c|}}{{{name}}} &\n'
        entry += f'\\cline{{2-{ilen+1}}}\n&\n\n'
        type_entries += entry

    # for each entry in the dataset create a table
    content = ''
    for (ext_list, title, filter_list, include_pseudo) in dataset:
        instr_dict = {}

        # for all extensions list in ext_list, create a dictionary of
        # instructions associated with those extensions.
        for e in ext_list:
            instr_dict.update(create_inst_dict(['rv'+e], include_pseudo))

        # if filter_list is not empty then use that as the official set of
        # instructions that need to be dumped into the latex table
        inst_list = list(instr_dict.keys()) if not filter_list else filter_list

        # for each instruction create an latex table entry just like how we did
        # above with the instruction-type table.
        instr_entries = ''
        for inst in inst_list:
            if inst not in instr_dict:
                logging.error(f'in make_ext_latex_table: Instruction: {inst} not found in instr_dict')
                raise SystemExit(1)
            fields = []

            # only if the argument is available in arg_lut we consume it, else
            # throw error.
            for f in instr_dict[inst]['variable_fields']:
                if f not in arg_lut:
                    logging.error(f'Found variable {f} in instruction {inst} whose mapping is not available')
                    raise SystemExit(1)
                (msb,lsb) = arg_lut[f]
                name = f.replace('_','.') if f not in latex_mapping else latex_mapping[f]
                fields.append((msb, lsb, name))

            msb = ilen -1
            y = ''
            if ilen == 16:
                encoding = instr_dict[inst]['encoding'][16:]
            else:
                encoding = instr_dict[inst]['encoding']
            for r in range(0,ilen):
                x = encoding [r]
                if ((msb, ilen-1-r+1)) in latex_fixed_fields:
                    fields.append((msb,ilen-1-r+1,y))
                    msb = ilen-1-r
                    y = ''
                if x == '-':
                    if y != '':
                        fields.append((msb,ilen-1-r+1,y))
                        y = ''
                    msb = ilen-1-r-1
                else:
                    y += str(x)
                if r == ilen-1:
                    if y != '':
                        fields.append((msb, 0, y))
                    y = ''

            fields.sort(key=lambda y: y[0], reverse=True)
            entry = ''
            for r in range(len(fields)):
                (msb, lsb, name) = fields[r]
                if r == len(fields)-1:
                    entry += f'\\multicolumn{{{msb - lsb + 1}}}{{|c|}}{{{name}}} & {inst.upper().replace("_",".")} \\\\\n'
                elif r == 0:
                    entry += f'\\multicolumn{{{msb - lsb + 1}}}{{|c|}}{{{name}}} &\n'
                else:
                    entry += f'\\multicolumn{{{msb - lsb + 1}}}{{c|}}{{{name}}} &\n'
            entry += f'\\cline{{2-{ilen+1}}}\n&\n\n'
            instr_entries += entry

        # once an entry of the dataset is completed we create the whole table
        # with the title of that dataset as sub-heading (sort-of)
        if title != '':
            content += f'''

\\multicolumn{{{ilen}}}{{c}}{{}} & \\\\
\\multicolumn{{{ilen}}}{{c}}{{\\bf {title} }} & \\\\
\\cline{{2-{ilen+1}}}

            &
{instr_entries}
'''
        else:
            content += f'''
{instr_entries}
'''


    header = f'''
\\newpage

\\begin{{table}}[p]
\\begin{{small}}
\\begin{{center}}
    \\begin{{tabular}} {{{column_size}l}}
    {" ".join(['&']*ilen)} \\\\

            &
{type_entries}
'''
    endtable=f'''

\\end{{tabular}}
\\end{{center}}
\\end{{small}}
{caption}
\\end{{table}}
'''
    # dump the contents and return
    latex_file.write(header+content+endtable)

def instr_dict_2_extensions(instr_dict):
    extensions = []
    for item in instr_dict.values():
        if item['extension'][0] not in extensions:
            extensions.append(item['extension'][0])
    return extensions

def make_chisel(instr_dict, spinal_hdl=False):

    chisel_names=''
    cause_names_str=''
    csr_names_str = ''
    for i in instr_dict:
        if spinal_hdl:
            chisel_names += f'  def {i.upper().replace(".","_"):<18s} = M"b{instr_dict[i]["encoding"].replace("-","-")}"\n'
        # else:
        #     chisel_names += f'  def {i.upper().replace(".","_"):<18s} = BitPat("b{instr_dict[i]["encoding"].replace("-","?")}")\n'
    if not spinal_hdl:
        extensions = instr_dict_2_extensions(instr_dict)
        for e in extensions:
            e_instrs = filter(lambda i: instr_dict[i]['extension'][0] == e, instr_dict)
            if "rv64_" in e:
                e_format = e.replace("rv64_", "").upper() + "64"
            elif "rv32_" in e:
                e_format = e.replace("rv32_", "").upper() + "32"
            elif "rv_" in e:
                e_format = e.replace("rv_", "").upper()
            else:
                e_format = e.upper
            chisel_names += f'  val {e_format+"Type"} = Map(\n'
            for instr in e_instrs:
                tmp_instr_name = '"'+instr.upper().replace(".","_")+'"'
                chisel_names += f'   {tmp_instr_name:<18s} -> BitPat("b{instr_dict[instr]["encoding"].replace("-","?")}"),\n'
            chisel_names += f'  )\n'

    for num, name in causes:
        cause_names_str += f'  val {name.lower().replace(" ","_")} = {hex(num)}\n'
    cause_names_str += '''  val all = {
    val res = collection.mutable.ArrayBuffer[Int]()
'''
    for num, name in causes:
        cause_names_str += f'    res += {name.lower().replace(" ","_")}\n'
    cause_names_str += '''    res.toArray
  }'''

    for num, name in csrs+csrs32:
        csr_names_str += f'  val {name} = {hex(num)}\n'
    csr_names_str += '''  val all = {
    val res = collection.mutable.ArrayBuffer[Int]()
'''
    for num, name in csrs:
        csr_names_str += f'''    res += {name}\n'''
    csr_names_str += '''    res.toArray
  }
  val all32 = {
    val res = collection.mutable.ArrayBuffer(all:_*)
'''
    for num, name in csrs32:
        csr_names_str += f'''    res += {name}\n'''
    csr_names_str += '''    res.toArray
  }'''

    if spinal_hdl:
        chisel_file = open('inst.spinalhdl','w')
    else:
        chisel_file = open('inst.chisel','w')
    chisel_file.write(f'''
/* Automatically generated by parse_opcodes */
object Instructions {{
{chisel_names}
}}
object Causes {{
{cause_names_str}
}}
object CSRs {{
{csr_names_str}
}}
''')
    chisel_file.close()

def make_rust(instr_dict):
    mask_match_str= ''
    for i in instr_dict:
        mask_match_str += f'const MATCH_{i.upper().replace(".","_")}: u32 = {(instr_dict[i]["match"])};\n'
        mask_match_str += f'const MASK_{i.upper().replace(".","_")}: u32 = {(instr_dict[i]["mask"])};\n'
    for num, name in csrs+csrs32:
        mask_match_str += f'const CSR_{name.upper()}: u16 = {hex(num)};\n'
    for num, name in causes:
        mask_match_str += f'const CAUSE_{name.upper().replace(" ","_")}: u8 = {hex(num)};\n'
    rust_file = open('inst.rs','w')
    rust_file.write(f'''
/* Automatically generated by parse_opcodes */
{mask_match_str}
''')
    rust_file.close()

def make_sverilog(instr_dict):
    names_str = ''
    for i in instr_dict:
        names_str += f"  localparam [31:0] {i.upper().replace('.','_'):<18s} = 32'b{instr_dict[i]['encoding'].replace('-','?')};\n"
    names_str += '  /* CSR Addresses */\n'
    for num, name in csrs+csrs32:
        names_str += f"  localparam logic [11:0] CSR_{name.upper()} = 12'h{hex(num)[2:]};\n"

    sverilog_file = open('inst.sverilog','w')
    sverilog_file.write(f'''
/* Automatically generated by parse_opcodes */
package riscv_instr;
{names_str}
endpackage
''')
    sverilog_file.close()
def make_c(instr_dict):
    mask_match_str = ''
    declare_insn_str = ''
    for i in instr_dict:
        mask_match_str += f'#define MATCH_{i.upper().replace(".","_")} {instr_dict[i]["match"]}\n'
        mask_match_str += f'#define MASK_{i.upper().replace(".","_")} {instr_dict[i]["mask"]}\n'
        declare_insn_str += f'DECLARE_INSN({i.replace(".","_")}, MATCH_{i.upper().replace(".","_")}, MASK_{i.upper().replace(".","_")})\n'

    csr_names_str = ''
    declare_csr_str = ''
    for num, name in csrs+csrs32:
        csr_names_str += f'#define CSR_{name.upper()} {hex(num)}\n'
        declare_csr_str += f'DECLARE_CSR({name}, CSR_{name.upper()})\n'

    causes_str= ''
    declare_cause_str = ''
    for num, name in causes:
        causes_str += f"#define CAUSE_{name.upper().replace(' ', '_')} {hex(num)}\n"
        declare_cause_str += f"DECLARE_CAUSE(\"{name}\", CAUSE_{name.upper().replace(' ','_')})\n"

    arg_str = ''
    for name, rng in arg_lut.items():
        begin = rng[1]
        end   = rng[0]
        mask = ((1 << (end - begin + 1)) - 1) << begin
        arg_str += f"#define INSN_FIELD_{name.upper().replace(' ', '_')} {hex(mask)}\n"

    with open(f'{os.path.dirname(__file__)}/encoding.h', 'r') as file:
        enc_header = file.read()

    commit = os.popen('git log -1 --format="format:%h"').read()
    enc_file = open('encoding.out.h','w')
    enc_file.write(f'''/* SPDX-License-Identifier: BSD-3-Clause */

/* Copyright (c) 2023 RISC-V International */

/*
 * This file is auto-generated by running 'make' in
 * https://github.com/riscv/riscv-opcodes ({commit})
 */

{enc_header}
/* Automatically generated by parse_opcodes. */
#ifndef RISCV_ENCODING_H
#define RISCV_ENCODING_H
{mask_match_str}
{csr_names_str}
{causes_str}
{arg_str}#endif
#ifdef DECLARE_INSN
{declare_insn_str}#endif
#ifdef DECLARE_CSR
{declare_csr_str}#endif
#ifdef DECLARE_CAUSE
{declare_cause_str}#endif
''')
    enc_file.close()

def make_go(instr_dict):

    args = " ".join(sys.argv)
    prelude = f'''// Code generated by {args}; DO NOT EDIT.'''

    prelude += '''
package riscv

import "cmd/internal/obj"

type inst struct {
	opcode uint32
	funct3 uint32
	rs1    uint32
	rs2    uint32
	csr    int64
	funct7 uint32
}

func encode(a obj.As) *inst {
	switch a {
'''

    endoffile = '''  }
	return nil
}
'''

    instr_str = ''
    for i in instr_dict:
        enc_match = int(instr_dict[i]['match'],0)
        opcode = (enc_match >> 0) & ((1<<7)-1)
        funct3 = (enc_match >> 12) & ((1<<3)-1)
        rs1 = (enc_match >> 15) & ((1<<5)-1)
        rs2 = (enc_match >> 20) & ((1<<5)-1)
        csr = (enc_match >> 20) & ((1<<12)-1)
        funct7 = (enc_match >> 25) & ((1<<7)-1)
        instr_str += f'''  case A{i.upper().replace("_","")}:
    return &inst{{ {hex(opcode)}, {hex(funct3)}, {hex(rs1)}, {hex(rs2)}, {signed(csr,12)}, {hex(funct7)} }}
'''
        
    with open('inst.go','w') as file:
        file.write(prelude)
        file.write(instr_str)
        file.write(endoffile)

    try:
        import subprocess
        subprocess.run(["go", "fmt", "inst.go"])
    except:
        pass


def make_yaml(instr_dict):
    def get_yaml_long_name(instr_name):
        current_dir = os.path.dirname(os.path.realpath(__file__))
        synopsis_file = os.path.join(current_dir, "synopsis")
        
        if os.path.exists(synopsis_file):
            with open(synopsis_file, 'r') as f:
                lines = f.readlines()
                for line in lines:
                    parts = line.strip().split(' ', 1)
                    if len(parts) == 2 and parts[0].lower() == instr_name.lower():
                        return parts[1]
        
        return 'No synopsis available.'

    def get_yaml_description(instr_name):
        current_dir = os.path.dirname(os.path.realpath(__file__))
        desc_file = os.path.join(current_dir, "description")

        if os.path.exists(desc_file):
            with open(desc_file, 'r') as f:
                lines = f.readlines()
                # Skip the first line as it's the header
                for line in lines[1:]:
                    parts = line.strip().split(' ', 1)
                    if len(parts) == 2 and parts[0].lower() == instr_name.lower():
                        return parts[1]
        
        return "No description available."
        

    def get_yaml_assembly(instr_name, instr_dict):
        instr_data = instr_dict.get(instr_name, {})
        var_fields = instr_data.get('variable_fields', [])

        reg_args = []
        imm_args = []

        for field in var_fields:
            mapped_field = asciidoc_mapping.get(field, field)
            if ('imm') in field:
                imm_args.append(mapped_field)
            else:
                reg_args.append(mapped_field.replace('rs', 'xs').replace('rd', 'xd'))

        # Combine immediate fields
        combined_imm = combine_imm_fields(imm_args)

        # Combine all arguments, registers first then immediates
        all_args = reg_args + (['imm'] if combined_imm else []) #substitute 'imm' with combined imm for precise imm description i.e. imm[12:0]

        # Create the assembly string
        assembly = f"{', '.join(all_args)}" if all_args else instr_name.lower()

        return assembly

    def process_extension(ext):
        parts = ext.split('_')
        if len(parts) == 2:
            return [parts[1].capitalize()]
        elif len(parts) == 3:
            return [parts[1].capitalize(), parts[2].capitalize()]
        else:
            return [ext.capitalize()]  # fallback for unexpected formats

    def make_yaml_encoding(instr_name, instr_data):
        encoding = instr_data['encoding']
        var_fields = instr_data.get('variable_fields', [])
        
        match = ''.join([bit if bit != '-' else '-' for bit in encoding])
        
        variables = []
        for field_name in var_fields:
            if field_name in arg_lut:
                start_bit, end_bit = arg_lut[field_name]
                variables.append({
                    'name': field_name,
                    'location': f'{start_bit}-{end_bit}',
                    'start-bit': start_bit,
                    'end_bit':end_bit
                })
        
        # Sort variables in descending order based on the start of the bit range
        variables.sort(key=lambda x: int(x['location'].split('-')[0]), reverse=True)
        
        result = {
            'match': match,
            'variables': variables
        }
        
        return result
    
    def get_yaml_encoding_diff(instr_data_original, pseudo_instructions):
        def get_variables(instr_data):
            encoding = instr_data['encoding']
            var_fields = instr_data.get('variable_fields', [])
            
            variables = {}
            for field_name in var_fields:
                if field_name in arg_lut:
                    start_bit, end_bit = arg_lut[field_name]
                    variables[field_name] = {
                        'field_name': field_name,
                        'match': encoding[31-start_bit:32-end_bit],
                        'start_bit': start_bit,
                        'end_bit': end_bit
                    }
            return variables

        original_vars = get_variables(instr_data_original)
        differences = {}

        for pseudo_name, pseudo_data in pseudo_instructions.items():
            pseudo_vars = get_variables(pseudo_data)
            field_differences = {}

            # Find fields that are different or unique to each instruction
            all_fields = set(original_vars.keys()) | set(pseudo_vars.keys())
            for field in all_fields:
                if field not in pseudo_vars:
                    field_differences[field] = {
                        'pseudo_value': pseudo_data['encoding'][31-original_vars[field]['start_bit']:32-original_vars[field]['end_bit']]
                    }
                elif field not in original_vars:
                    field_differences[field] = {
                        'pseudo_value': pseudo_vars[field]['match']
                    }
                elif original_vars[field]['match'] != pseudo_vars[field]['match']:
                    field_differences[field] = {
                        'pseudo_value': pseudo_vars[field]['match']
                    }

            if field_differences:
                differences[pseudo_name] = field_differences

        return differences

    def get_yaml_definedby(instr_data):
        defined_by = set()
        for ext in instr_data['extension']:
            parts = ext.split('_')
            if len(parts) > 1:
                # Handle cases like 'rv32_d_zicsr'
                for part in parts[1:]:
                    defined_by.add(part.capitalize())
            else:
                defined_by.add(ext.capitalize())
        
        return f"[{', '.join(sorted(defined_by))}]"



    def get_yaml_base(instr_data):
        for ext in instr_data['extension']:
            if ext.startswith('rv32'):
                return 32
            elif ext.startswith('rv64'):
                return 64
        return None


    # Group instructions by extension
    extensions = {}
    rv32_instructions = {}
    for instr_name, instr_data in instr_dict.items():
        if instr_name.endswith('_rv32'):
            base_name = instr_name[:-5]
            rv32_instructions[base_name] = instr_name
        else:
            for ext in instr_data['extension']:
                ext_letters = process_extension(ext)
                for ext_letter in ext_letters:
                    if ext_letter not in extensions:
                        extensions[ext_letter] = {}
                    extensions[ext_letter][instr_name] = instr_data


    # Create a directory to store the YAML files
    base_dir = 'yaml_output'
    os.makedirs(base_dir, exist_ok=True)

    # Generate and save YAML for each extension
    for ext, ext_dict in extensions.items():
        ext_dir = os.path.join(base_dir, ext)
        os.makedirs(ext_dir, exist_ok=True)
    
        
        for instr_name, instr_data in ext_dict.items():
            yaml_content = {}
            instr_name_with_periods = instr_name.replace('_', '.')
            yaml_content[instr_name_with_periods] = {
                'long_name': get_yaml_long_name(instr_name),
                'description': get_yaml_description(instr_name),
                'definedBy': get_yaml_definedby(instr_data),
                'base': get_yaml_base(instr_data),
                'assembly': get_yaml_assembly(instr_name, instr_dict),
                'encoding': make_yaml_encoding(instr_name, instr_data),
                'access': {
                            's': '',
                            'u': '',
                            'vs': '',
                            'vu': ''
                }
            }

            # Add pseudoinstruction field for origin instructions
            if 'pseudo_ops' in instr_data:
                pseudo_list = [pseudo.replace('_', '.') for pseudo in instr_data['pseudo_ops']]
                if pseudo_list:
                    yaml_content[instr_name_with_periods]['pseudoinstructions'] = []
                    pseudo_instructions = {pseudo.replace('.', '_'): instr_dict[pseudo.replace('.', '_')] for pseudo in pseudo_list}
                    encoding_diffs = get_yaml_encoding_diff(instr_data, pseudo_instructions)
                    for pseudo in pseudo_list:
                        assembly = get_yaml_assembly(pseudo.replace('.', '_'), instr_dict)
                        diff_info = encoding_diffs.get(pseudo.replace('.', '_'), {})
                        when_condition = get_yaml_assembly(instr_name, instr_dict).replace(assembly,"").replace(",","")
                        if diff_info:
                            diff_str = ", ".join([f"{field}=={details['pseudo_value']}" for field, details in diff_info.items()])
                            when_condition = f"{diff_str}"
                        yaml_content[instr_name_with_periods]['pseudoinstructions'].append({
                            'when': when_condition,
                            'to': f"{pseudo} {assembly}",
                        })
            
            
            #  Add origininstruction field for pseudo instructions
            if instr_data.get('is_pseudo', False):
                yaml_content[instr_name_with_periods]['origininstruction'] = instr_data['orig_inst'].replace('_', '.')

            # Add operation field last
            yaml_content[instr_name_with_periods]['operation'] = None

            # Handle encoding for RV32 and RV64 versions
            if instr_name in rv32_instructions:
                yaml_content[instr_name_with_periods]['encoding'] = {
                    'RV32': make_yaml_encoding(rv32_instructions[instr_name], instr_dict[rv32_instructions[instr_name]]),
                    'RV64': make_yaml_encoding(instr_name, instr_data)
                }
            else:
                yaml_content[instr_name_with_periods]['encoding'] = make_yaml_encoding(instr_name, instr_data)

            if yaml_content[instr_name_with_periods]['base'] is None or (instr_name in rv32_instructions):
                yaml_content[instr_name_with_periods].pop('base')


        
            yaml_string = "# yaml-language-server: $schema=../../../schemas/inst_schema.json\n\n"
            yaml_string += yaml.dump(yaml_content, default_flow_style=False, sort_keys=False)
            yaml_string = yaml_string.replace("'[", "[").replace("]'","]").replace("'-","-").replace("0'","0").replace("1'","1").replace("-'","-")
            yaml_string = re.sub(r'description: (.+)', lambda m: f'description: |\n      {m.group(1)}', yaml_string)
            yaml_string = re.sub(r'operation: (.+)', lambda m: f'operation(): |\n      {""}', yaml_string)



            # Write to file
            filename = f'{instr_name_with_periods}.yaml'
            filepath = os.path.join(ext_dir, filename)
            with open(filepath, 'w') as outfile:
                outfile.write(yaml_string)
    
    print("Summary of all extensions saved as yaml_output/extensions_summary.yaml")


def signed(value, width):
  if 0 <= value < (1<<(width-1)):
    return value
  else:
    return value - (1<<width)


if __name__ == "__main__":
    print(f'Running with args : {sys.argv}')

    extensions = sys.argv[1:]
    for i in ['-c','-latex','-chisel','-sverilog','-rust', '-go', '-spinalhdl','-asciidoc', '-yaml']:
        if i in extensions:
            extensions.remove(i)
    print(f'Extensions selected : {extensions}')

    include_pseudo = False
    if "-go" in sys.argv[1:]:
        include_pseudo = True

    instr_dict = create_inst_dict(extensions, include_pseudo=True)
    with open('instr_dict.yaml', 'w') as outfile:
        yaml.dump(instr_dict, outfile, default_flow_style=False)
    instr_dict = collections.OrderedDict(sorted(instr_dict.items()))

    if '-c' in sys.argv[1:]:
        instr_dict_c = create_inst_dict(extensions, False, 
                                        include_pseudo_ops=emitted_pseudo_ops)
        instr_dict_c = collections.OrderedDict(sorted(instr_dict_c.items()))
        make_c(instr_dict_c)
        logging.info('encoding.out.h generated successfully')

    if '-chisel' in sys.argv[1:]:
        make_chisel(instr_dict)
        logging.info('inst.chisel generated successfully')

    if '-spinalhdl' in sys.argv[1:]:
        make_chisel(instr_dict, True)
        logging.info('inst.spinalhdl generated successfully')

    if '-sverilog' in sys.argv[1:]:
        make_sverilog(instr_dict)
        logging.info('inst.sverilog generated successfully')

    if '-rust' in sys.argv[1:]:
        make_rust(instr_dict)
        logging.info('inst.rs generated successfully')

    if '-go' in sys.argv[1:]:
        make_go(instr_dict)
        logging.info('inst.go generated successfully')

    if '-latex' in sys.argv[1:]:
        make_latex_table()
        logging.info('instr-table.tex generated successfully')
        make_priv_latex_table()
        logging.info('priv-instr-table.tex generated successfully')

    if '-yaml' in sys.argv[1: ]:
        make_yaml(instr_dict)
        logging.info('instr.yaml generated succesfully')

    if '-asciidoc' in sys.argv[1:]:
        extension_content, instruction_list = make_asciidoc_instructions(instr_dict)
        
        # Write each extension to a separate file
        for ext, content in extension_content.items():
            filename = f'instr-encoding-{ext}.adoc'
            with open(filename, 'w') as adoc_file:
                adoc_file.write(f"== {ext.upper()} Extension\n\n")
                adoc_file.write(content)
            logging.info(f'{filename} generated successfully')
        
        # Write reference table to a file
        reference_table = make_asciidoc_reference_table(instruction_list)
        with open('instr-reference-table.adoc', 'w') as adoc_file:
            adoc_file.write(reference_table)
        logging.info('instr-reference-table.adoc generated successfully')

        # Generate a main include file
        with open('instr-encoding-all.adoc', 'w') as adoc_file:
            adoc_file.write("= RISC-V Instruction Encoding\n\n")
            adoc_file.write("include::instr-reference-table.adoc[]\n\n")
            for ext in sorted(extension_content.keys()):
                adoc_file.write(f"include::instr-encoding-{ext}.adoc[]\n")
        logging.info('instr-encoding-all.adoc generated successfully')
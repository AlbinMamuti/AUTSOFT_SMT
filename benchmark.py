#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from io import StringIO
import json
from random import randint, random

from pysmt.smtlib.parser import SmtLibParser
from pysmt.walkers import TreeWalker, IdentityDagWalker
from pysmt.rewritings import CNFizer
from pysmt.shortcuts import *
from equiv_walker import RandomEquivDagWalker
from pysmt.exceptions import SolverReturnedUnknownResultError
import tqdm
import datetime

from prop_walker import RandomWeakenerDagWalker
from strengthener_walker import RandomStrengthenerDagWalker
from symbol_walker import SymbolDagWalker

import os
import re
import sys
import time
import numpy
import requests
import traceback
import multiprocessing
import pysmt


CPUs = multiprocessing.cpu_count()

def iterate_equivalence(formula,walker,symbols,logic,solver):
    data_point = []
    # formula, change, is_sat_ret
    
    #seen_formulas = 
    
    walked = formula
    for i in range(20):
        old_walked = walked
        walked = walker.change_once(walked,symbols,old_walked)
        if old_walked == walked:
            break
        start = time.time()
        ret = is_sat(walked,solver_name=solver)
        end = time.time()
        data_point.append([walked,walker.change_id,ret,"equiv",logic,solver,end - start])
    return data_point

def iterate_strength_weaken(formula,s_walker,w_walker,symbols,logic,solver):
    data_point = []
    # formula, change, is_sat_ret
    walkers = [w_walker,s_walker]
    walkers_descr = ["weaken","strengthen"]
    walked = formula
    for i in range(10):
        coin_flip = randint(0,1)
        walker = walkers[coin_flip]
        
        old_walked = walked
        
        walked = walker.change_once(walked,symbols,old_walked)
        
        if old_walked == walked:
            break
        start = time.time()
        try:
            ret = is_sat(walked,solver_name=solver)
        except SolverReturnedUnknownResultError as e:
            end = time.time()
            ret = "unkown"
        end = time.time()
        data_point.append([walked,walker.change_id,ret,walkers_descr[coin_flip],logic,solver,end - start])
    return data_point

def iterate_strength_weaken_equiv(formula,s_walker,w_walker,e_walker,symbols,logic,solver):
    data_point = []
    # formula, change, is_sat_ret, walker, logic
    walkers = [w_walker,s_walker,e_walker]
    walkers_descr = ["weaken","strengthen","equiv"]
    walked = formula
    for i in range(10):
        coin_flip = randint(0,2)
        walker = walkers[coin_flip]
        
        old_walked = walked
        
        walked = walker.change_once(walked,symbols,old_walked)
        
        if old_walked == walked:
            break
        start = time.time()
        ret = is_sat(walked,solver_name=solver)
        end = time.time()
        data_point.append([formula_to_smtlib_string(walked),walker.change_id,ret,walkers_descr[coin_flip],logic,solver,end - start])
    return data_point

def formula_from_smtlib_string(str):
    script = parser.get_script(StringIO(str))
    return script.get_last_formula()


def formula_to_smtlib_string(formula):
    return formula.to_smtlib(daggify=True)

def analyze_block(formula):
    
    
    prop_walker = RandomWeakenerDagWalker(env=None,invalidate_memoization=True)
    symbol_walker = SymbolDagWalker(env=None,invalidate_memoization=True)
    strength_walker = RandomStrengthenerDagWalker(env=None,invalidate_memoization=True)
    equiv_walker = RandomEquivDagWalker(env=None,invalidate_memoization=True)
    
    dataZ3 = []
    dataCVC4 = []
    
    form = formula[0]
    form = equiv_walker.walk(form)
    try:
        symbols = symbol_walker.get_symbols(form)
        solver_name="z3"
        dataZ3.append( [*[iterate_equivalence(form,equiv_walker,symbols,formula[2],solver_name)],formula[1]])
        dataZ3.append( [*[iterate_strength_weaken(form,strength_walker,prop_walker,symbols,formula[2],solver_name)],formula[1]])
        dataZ3.append( [*[iterate_strength_weaken_equiv(form,strength_walker,prop_walker,equiv_walker, symbols,formula[2],solver_name)],formula[1]])

        solver_name="cvc4"
        dataCVC4.append( [*[iterate_equivalence(form,equiv_walker,symbols,formula[2],solver_name)],formula[1]])
        dataCVC4.append( [*[iterate_strength_weaken(form,strength_walker,prop_walker,symbols,formula[2],solver_name)],formula[1]])
        dataCVC4.append( [*[iterate_strength_weaken_equiv(form,strength_walker,prop_walker,equiv_walker, symbols,formula[2],solver_name)],formula[1]])

        return 1
    except Exception as e:
        import traceback
        print(traceback.format_exc())
        print(e)
        return 0
    
        # except Exception as e:
        #     print(colors.FAIL+str(traceback.format_exc())+colors.END)
        #     print(colors.FAIL+"Error: "+str(e)+" @ block number: "+str(block_number)+colors.END)
        #     end = time.time()
        #     return end - start

     

    end = time.time()
    return end - start

def init_process():
    
    return

def parse():
    global parser
    data = []
    parser = SmtLibParser()
    #data is of the form [formula, sat/unsat]
    
    path = "semantic-fusion-seeds-master/"

    logics = ["QF_LIA"]#,"LIA","QF_LRA","LRA","QF_NRA","NRA"]

    for logic in logics:
        path_to_logic = path + logic + "/"
        
        for sat_unsat in ["sat","unsat"]:
            
            directory = os.fsencode(path_to_logic+sat_unsat)
    
            for file in os.listdir(directory):
                filename = os.fsdecode(file)
                filepath = os.fspath(file)
                if filename.endswith(".smt2"): 
                    # print(os.path.join(directory, filename))
                    with open(path_to_logic+sat_unsat+"/"+filename,"r") as f:
                        try:
                            script = parser.get_script(f)
                            formula = script.get_last_formula()
                            data.append([formula,sat_unsat,logic])
                        except:
                            pass
                else:
                    continue
    return data
def main():
    
    data = parse()
    
    if sys.platform.startswith("linux"):
        multiprocessing.set_start_method("fork", force=True)
        
    print("Running analysis of SMT Solver for Z3 and CVC4")
    print("Initializing workers...")
    execution_times=[]
    analyze_block(data[0])
    with multiprocessing.Pool(processes=CPUs, initializer=init_process, initargs=()) as pool:
        start_total = time.time()
        
        for execution_time in (pbar:=tqdm.tqdm(pool.map(analyze_block, data, ),desc="Formulas", total= len(data),bar_format="{l_bar}{bar} [ time left: {remaining}, time spent: {elapsed}]")):
                execution_times.append(execution_time)
                pbar.set_description(f'Nr Analyzed: {len(execution_times)}; Current Time: {datetime.now()}')
                pbar.update()
        end_total = time.time()
        
        
        print("Total execution time: ")
        print()
        if execution_times:
            print("Max execution time: ")
            print("Mean execution time: ")
            print("Median execution time")
            print("Min execution time: ")

if __name__ == "__main__":
    main()
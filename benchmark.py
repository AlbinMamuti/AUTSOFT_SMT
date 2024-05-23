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

def iterate_equivalence(formula,walker,symbols,is_sat):
    data_point = []
    # formula, change, is_sat_ret
    
    #seen_formulas = 
    
    walked = formula
    for i in range(20):
        old_walked = walked
        walked = walker.change_once(walked,symbols,old_walked)
        if old_walked == walked:
            break
        ret = is_sat()
        data_point.append([walked,walker.change_id,ret,"equiv"])

def iterate_strength_weaken(formula,s_walker,w_walker,symbols,is_sat):
    data_point = []
    # formula, change, is_sat_ret
    walkers = [w_walker,s_walker]
    walkers_descr = ["weaken","strengthen"]
    walked = formula
    for i in range(100):
        coin_flip = randint(0,1)
        walker = walkers[coin_flip]
        
        old_walked = walked
        
        walked = walker.change_once(walked,symbols,old_walked)
        
        if old_walked == walked:
            break
        ret = is_sat()
        data_point.append([walked,walker.change_id,ret,walkers_descr[coin_flip]])

def iterate_strength_weaken_equiv(formula,s_walker,w_walker,e_walker,symbols,is_sat):
    data_point = []
    # formula, change, is_sat_ret
    walkers = [w_walker,s_walker,e_walker]
    walkers_descr = ["weaken","strengthen","equiv"]
    walked = formula
    for i in range(100):
        coin_flip = randint(0,2)
        walker = walkers[coin_flip]
        
        old_walked = walked
        
        walked = walker.change_once(walked,symbols,old_walked)
        
        if old_walked == walked:
            break
        ret = is_sat()
        data_point.append([walked,walker.change_id,ret,walkers_descr[coin_flip]])

def analyze_block(formula):
    
    
    prop_walker = RandomWeakenerDagWalker(env=None,invalidate_memoization=True)
    symbol_walker = SymbolDagWalker(env=None,invalidate_memoization=True)
    strength_walker = RandomStrengthenerDagWalker(env=None,invalidate_memoization=True)
    equiv_walker = RandomEquivDagWalker(env=None,invalidate_memoization=True)
    
    start = time.time()
    
    
    try:
        
        
        return
    except:
        return time.time() - start
    
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
                            data.append([formula,sat_unsat])
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
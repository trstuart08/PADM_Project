# -*- coding: utf-8 -*-
"""
Created on Sun Nov 14 04:22:11 2021

@author: Tom Stuart [thoma]
"""

from math import *
import numpy as np
import random as random
import copy
import itertools

'''
Component class, Proposition class, Clause class, and Model class definition
'''
class Component:
    '''
    Component(name, domain, probs, assignable): class to represent components in our model
    
    name..........string to identify the name of the component, should be defined to match the string used in any corresponding propositions
    domain........possible modes of the component, should be defined to match the modes used in any propositions or clauses (tuple)
    probs.........the (prior) probability associated with each domain value (tuple)
    asssignable...if domain is a single value, then assignable is False, otherwise it is True for hardware components and should be declared as False for intermediate variables
    '''
    def __init__(self, name, domain, probs, assignable):
        self.name = name
        self.domain = domain
        self.probs = probs
        if len(self.domain) == 1:
            self.assignable = False
        else:
            self.assignable = assignable
    
    def __str__(self):
        if self.assignable:
            val = 'assignable'
        else:
            val = 'unassignable'
        return '( {self.name}, {self.domain}, {self.probs}, {val})'.format(self=self,val=val)
    
    def __repr__(self):
        if self.assignable:
            val = 'assignable'
        else:
            val = 'unassignable'
        return 'Component Class ( {self.name}, {self.domain}, {self.probs}, {val})'.format(self=self,val=val)
    
    def get_remaining_propositions(self, domain_modes_to_exclude = []):
        '''
       Component.get_max_proposition(domain_vals_to_exclude): Returns the proposition that has the maximum prior probability. Excludes component domain modes in domain_modes_to_exclude, if provided
        
        domain_modes_to_exclude.............a list of component modes that should be excluded from the search for maximum prior probability
                
        Returns:
            corr_proposition........A Proposition class variable corresponding that has the maximum probability out of the domain defined by excluding the domain_modes_to_exclude from the component domain

            
        '''
        if not domain_modes_to_exclude:
            corr_propositions = set()
            for mode in self.domain:
                corr_propositions.add(Proposition(self.name, mode, self))
            return corr_propositions
        else:
            corr_propositions = set()
            possible_domain = list(self.domain)
            # remove excluded vals from search space
            for val in domain_modes_to_exclude:
                possible_domain.remove(val)
            for mode in possible_domain:
                corr_propositions.add(Proposition(self.name, mode, self))
            return corr_propositions    
    
    def get_max_proposition(self, domain_modes_to_exclude = []):
        '''
       Component.get_max_proposition(domain_vals_to_exclude): Returns the proposition that has the maximum prior probability. Excludes component domain modes in domain_modes_to_exclude, if provided
        
        domain_modes_to_exclude.............a list of component modes that should be excluded from the search for maximum prior probability
                
        Returns:
            corr_proposition........A Proposition class variable corresponding that has the maximum probability out of the domain defined by excluding the domain_modes_to_exclude from the component domain

            
        '''
        if not domain_modes_to_exclude:
            max_prob = max(self.probs)
            max_index = self.probs.index(max_prob)
            corr_proposition = Proposition(self.name, self.domain[max_index])
            return corr_proposition
        else:
            possible_domain = list(self.domain)
            possible_probs = list(self.probs)
            # remove excluded vals from search space
            for val in domain_modes_to_exclude:
                rem_val_index = possible_domain.index(val)
                possible_domain.remove(val)
                possible_probs.pop(rem_val_index)
            max_prob = max(possible_probs)
            max_index = possible_probs.index(max_prob)
            corr_proposition = Proposition(self.name, possible_domain[max_index], self)
            return corr_proposition
    
    def get_max_prob(self, domain_modes_to_exclude = []):
        '''
       Component.get_max_prob(domain_vals_to_exclude): Returns probability associated with the component mode that has the maximum prior probability after excluding component domain modes in domain_modes_to_exclude (if provided)
        
        domain_modes_to_exclude.............a list of component modes that should be excluded from the search for maximum prior probability
        
        Returns:
            max_prob........ the probability associated with the component mode that has the maximum probability out of the domain defined by excluding the domain_modes_to_exclude from the component domain

            
        '''
        
        if not domain_modes_to_exclude:
            max_prob = max(self.probs)
            return max_prob
        else:
            possible_domain = list(self.domain)
            possible_probs = list(self.probs)
            # remove excluded vals from search space
            for val in domain_modes_to_exclude:
                rem_val_index = possible_domain.index(val)
                possible_domain.remove(val)
                possible_probs.pop(rem_val_index)
            max_prob = max(possible_probs)
            return max_prob
            
        

class Proposition:
    '''
    Proposition(name, mode, component, support = None): Class to represent logical propositions
    
    name...........string to identify the name of the proposition
    mode...........integer to identify the mode of the proposition that is True (e.g. 0, 1, 2)
    component......a Component class variable associated with the proposition
    support........a Clause class variable or the string "Given" denoting the evidence that supports the proposition
    
    Example: A1 = Proposition('A1',0) is a proposition that component A1 is in mode 0.

    
    
    '''
    def __init__(self, name, mode, component, support = None):
        self.name = name            # name is a string
        self.mode = mode            # mode is an integer with 0 representing False and 1 representing True
        self.component = component  # the component associated with the proposition, must be a Component class variable
        self.support = support      # The clause that supports the proposition

        # This attribute is the probability of the proposition mode for its associated component
        if self.mode in self.component.domain:
            prob_index = self.component.domain.index(self.mode)
            self.prob = self.component.probs[prob_index]
        else:
            self.prob = 0
        
    def __str__(self):
        return '(' + self.name + ', ' + str(self.mode) + ')'
    
    def __repr__(self):
        return 'Prop Class ({self.name}, {self.mode})'.format(self=self)
    
    def change_mode(self, new_mode):
        self.mode = new_mode
        return self
    
    def logical_test(self,candidate_mode):
        if candidate_mode == self.mode:
            return True
        else:
            return False

class Clause:
    '''
    Clause(name, props): class to represent logical clauses in conjunctive normal form
    
    name..........string to identify the clause
    props.........set of Proposition class variables

    NOTE: ropositions are assumed to be "OR" operators.
    '''
    def __init__(self, name, props = set()):
        self.name = name           # name is a string identifying the clause
        self.props = props         # props is a set of Proposition data types
        for prop in self.props:    # propositions that are part of a clause are supported by the clause
            prop.support = self
    
    def __repr__(self):
        output_str = 'Clause class {self.name} - '.format(self=self)
        num_props = len(self.props)
        count = 0
        for prop in self.props:
            count += 1
            output_str += str(prop)
            if count != num_props:
                output_str += ' OR '
        return output_str
    
    def __str__ (self):
        output_str = 'Clause {self.name} - '.format(self=self)
        num_props = len(self.props)
        count = 0
        for prop in self.props:
            count += 1
            output_str += str(prop)
            if count != num_props:
                output_str += ' OR '
        return output_str

class Model:
    '''
    Model(clauses): class to represent a model of logical clauses in conjunctive normal form (clauses are joined by AND statements)
    
    clauses.........set of Clause class variables
    
    Other attributes:
    -----------------
    
    components......set of components (Component class variables) in the model (one item for each unique component in a clause)

    NOTE: ropositions are assumed to be "OR" operators.
    '''
    def __init__(self, clauses):
        self.clauses = clauses
        components = set()
        for clause in clauses:
            for prop in clause.props:
                components.add(prop.component)
        self.components = components
    def __str__(self):
        output_str = ''
        num_clauses = len(self.clauses)
        count = 0
        for clause in self.clauses:
            count += 1
            output_str += '( ' + str(clause) + ' )'
            if count != num_clauses:
                output_str += ' AND '
        return output_str
    def __repr__(self):
        output_str = 'Model class - '
        num_clauses = len(self.clauses)
        count = 0
        for clause in self.clauses:
            output_str += '( '
            count += 1
            output_str += str(clause) + ' )'
            if count != num_clauses:
                output_str += ' AND '
        return output_str

'''
Functions dealing with propositions
'''

def compute_proposition_set_likelihood(propositions):
    likelihood = 1
    for prop in propositions:
        likelihood *= prop.prob
    return likelihood

def find_highest_probability_proposition(propositions, bias_mode1 = False):
    '''

    Parameters
    ----------
    propositions : list of Proposition class variables
    bias_mode1 : Boolean on whether or not want to give preference to propositions with a mode = 1 assignment over others that have an equal probability

    Returns
    -------
    A list of Proposition class variables
    
        If one of the propositions in the propositions list has the uniquely maximum associated probability, then that proposition is returned in the list. If multiple propositions have the same probability, then each is returned in a list.
        
        Otherwise, if bias_mode1 is True and if multiple propositions share a maximum probability value, and at least one has a mode = 1, value, then propositions with a mode of 1 are returned. Otherwise, if multiple propositions share the same probability and none are assigned a mode of 1, then all those propositions are returned.

    '''
    prop_probs = []
    prop_mode = []
    for prop in propositions:
        mode_index = prop.component.domain.index(prop.mode)
        prop_probs.append(prop.component.probs[mode_index])
        prop_mode.append(prop.mode)
    max_prob = max(prop_probs)
    max_indices = [idx for idx, prob in enumerate(prop_probs) if prob == max_prob]
    max_modes = []
    for idx in max_indices:
        max_modes.append(prop_mode[idx])    
    if len(max_indices) == 1:
        max_index = max_indices[0]
        return [propositions[max_index]]
    else:
        poss_props = []
        for idx in max_indices:
            poss_props.append(propositions[idx])
        if bias_mode1 == False:
            return poss_props
        
        # Give precedence to returning an assignment of mode 1
        else:
            mode1_indices = [idx for idx, mode in enumerate(max_modes) if mode == 1]
            if len(mode1_indices) == 1:
                return poss_props[mode1_indices[0]]
            elif mode1_indices:
                prop_choices = []
                for idx in mode1_indices:
                    prop_choices.append(props[idx])
                return prop_choices
            else:
                return poss_props
        
    
        
def assignable_propositions(propositions):
    '''
    Function to filter a list of propositions down to only those components that are assignable. Removes propositions associated with a components for which <component>.assignable is False from the list.
    
    Parameters
    ----------
    propositions : a list of Proposition class variables
    
    Returns
    -------
    filtered_propositions : a list of the Propositition class varaibles that were in the the input <propositions> for which <component>.assignable is not False
    '''
    filtered_propositions = set()
    for prop in propositions:
        if prop.component.assignable == True:
            filtered_propositions.add(prop)
    return filtered_propositions
    

def get_components(propositions):
    '''

    Parameters
    ----------
    propositions : list of Proposition class variables

    Returns
    -------
    component_names : a list of the names of the components contained in the propositions sharing the indices of the propositions list

    '''
    components = set()
    for prop in propositions:
        components.add(prop.component)
    return components

def get_component_modes(propositions):
    '''

    Parameters
    ----------
    propositions : a list of Proposition class variables
        DESCRIPTION.

    Returns
    -------
    component_modes : a list of the component modes of the propositions sharing the indices of the propositions list

    '''
    component_modes = []
    for prop in propositions:
        component_modes.append(prop.mode)
    return component_modes

'''
Satisfaction check / Conflict generation functions
'''

def generate_exhaustive_proposition_sets(model, candidate_propositions):
    '''

    Parameters
    ----------
    model : Model class variable
        The model for your system of interest.
    candidate_propositions : set of Proposition class variables
        These candidate_propositions will be compared against the Component class variables that are contained within the model. If there are components in the model that are not in candidate_propositions, then this function will generate all possible proposition assignments for the components that are missing from candidate_propositions. These assignments will then be used to generate an exhaustive list of all possible candidate_proposition sets.

    Returns
    -------
    all_can_props : list where each element is a set of Proposition class variables
        Each set is unique and contains a proposition corresponding to every component in the 

    '''
    can_prop_components = get_components(candidate_propositions)
    all_can_props = []
    poss_component_prop_sets = []
    # (1) Identify model components who do not have a corresponding proposition in candidate_propositions
    for model_component in model.components:
        no_match = True
        for can_component in can_prop_components:
            if can_component == model_component:
                no_match = False
                break
    # (2) If there is an unassigned model component, generate possible assignments for it
        if no_match:
            poss_component_prop_sets.append(model_component.get_remaining_propositions())
    # (3) Use the list of possible component assignment sets to generate all possible candidate proposition sets
    if poss_component_prop_sets:
         all_can_prop_bases = list(itertools.product(*poss_component_prop_sets))
         for prop_set in all_can_prop_bases:
             prop_set = set(prop_set)
             prop_set = prop_set.union(candidate_propositions)    # Combine the basis set with the candidate propositions
             all_can_props.append(prop_set)
    else:
        all_can_props.append(candidate_propositions)
    return all_can_props

def logical_test(clause, can_props, multi_can_sets = False, addl_can_props = [], debug_mode = False):
    '''
    logical_test(clause, can_props): Tests if the propositions in can_props are logically consistent with the clause.
    ----------------------------------------------------------------------
    Parameters
    ----------------------------------------------------------------------
    
    clause................a Clause class variable that will be tested for consistency with the propositions in can_props
    
    can_props.............a set of candidate propositions (recommend using a mutable type)
        
    debug_mode............ return a more exhaustive set of variables that include many intermediate variables if True
    
    NOTE: assumes that no two candidate propositions share the same name
    
    ----------------------------------------------------------------------
    Returns
    ----------------------------------------------------------------------
    
        conflicts...............If log_test_result is False, returns a list of the candidate propositions; will be an empty list if there are no conflicts
        
        can_props...............A set of proposition class variables, if the routine has added new candidates, then these are included, otherwise it is the same as the input
        
        
    ----------------------------------------------------------------------
    Additional returns if debug_mode = True
    ----------------------------------------------------------------------
        
        log_test_result.........False if all propositions in Clause.props are contradicted by a proposition in can_props
        clause_logic_list.......A list of logical statements with indices corresponding the the propositions in can_props
        hypo_assignments....If every candidate proposition conflicted with the clause, returns a list of the propositions in Clause that did not share a name with any candidate propositions (these propositions could be assigned a value can_props)

        
    '''
    # generate intermediate variables and initialize outputs
    conflicts = set()
    prop_list = []
    prop_combos_to_try = []
    for prop in clause.props:
        prop_list.append(prop)     # list corresponding to propositions in the set clause.props
    

    # (1) Identify propositions in the clause that are contradicted by can_props
    unassigned_list = []     # list with indices corresonding to prop_list
    clause_logic_list = []    # Each element is False if the corresponding proposition is not enforced by a can_prop
    unmatched_components = set()   # sett of components who do not have a proposition are assigned by can_props
    possible_conflicts = []
    prop_idx = 0
    for prop in prop_list:    # use the list for iteration to ensure consistent indexes!
        clause_logic_list.append(False)
        no_match_flag = True
        can_name_count = 0
        for can_prop in can_props:
            if can_prop.component == prop.component:
                no_match_flag = False
                can_name_count += 1
                # check to see if can_prop and prop share the same mode or conflict
                if can_prop.mode == prop.mode:
                    clause_logic_list[prop_idx] = True
                # warn if have multiple candidate props with the same name
                else:
                    possible_conflicts.append(can_prop)
                if can_name_count > 1:
                    print('Warning: multiple candidate propositions with the same component')
        # (2) Identify propositions in the clause whose component is unassigned by can_props
        if no_match_flag:
            unassigned_list.append(True)
            unmatched_components.add(prop.component)
        else:
            unassigned_list.append(False)
        prop_idx += 1
    
    # (3) If all clauses are satisfied, then log_test_result is True and there will be no need to assess the hypothetical assignments
    log_test_result = any(clause_logic_list)
    if log_test_result:
        #print('returning with log_test_result = True')
        if not debug_mode:
            return (conflicts, can_props)
        else:
            return (conflicts, can_props, log_test_result, clause_logic_list, unmatched_components)     
    
    # (4) if log_test_result is False, then we need to assess if any components are unassigned by cand_props, if they are then we can return hypothetical assignments and will need to call this function again
    elif any(unassigned_list):
        # (a) Get all ways to assign possible propositions
        poss_component_props = []
        for comp in unmatched_components:
            new_props = comp.get_remaining_propositions()
            for prop in new_props:
                prop.support = clause
            poss_component_props.append(new_props)
        prop_combos_to_try = list(itertools.product(*poss_component_props))
        print('\n')
        print(clause)
        print(prop_combos_to_try)
        # (b) Check each assignment combination for conflicts
        poss_conflicts = set()
        consistent_flag = False
        for prop_combo in prop_combos_to_try:
            addl_props = set(prop_combo)
            can_prop_try = addl_props.union(can_props)
            print(can_prop_try)
            trial_conflicts, trial_can_props = logical_test(clause, can_prop_try)
            print(trial_conflicts)
            if not trial_conflicts:
                consistent_flag = True
                conflicts = set()
                can_props = can_prop_try
                return conflicts, can_props
            else:
                poss_conflicts.union(trial_conflicts)
        if not consistent_flag:
            conflicts = conflicts.union(poss_conflicts)
        # (c) Return results
        if not debug_mode:
            return conflicts, can_props
        else:
            return conflicts, can_props, log_test_result, clause_logic_list, unmatched_components
    # (5) if log_test result is False and every element in unassigned_list is False, then we have identified conflicts
    else:
        # Conflicts are those propositions for which clause_logic_list is False and which are associated with an assignable component
        False_indices = [idx for idx, var in enumerate(clause_logic_list) if var == False]
        for idx in False_indices:
            if prop_list[idx].component.assignable:
                conflicts.add(prop_list[idx])
        # Additional conflicts are proposition assignments whose support does not correspond to a given (e.g. does NOT correspond to a known input or output value)
        for can_prop in can_props:
            if (can_prop.support != 'Given') and (can_prop.support != 'kernel'):    # can_prop.support is a Clause class variable or 'Given'
                #print('we are inside the support build')
                #print(can_prop.support)
                additional_conflicts = assignable_propositions(can_prop.support.props)
                #print(additional_conflicts)
                if additional_conflicts:
                    for prop in additional_conflicts:
                        conflicts.add(prop)
        if not debug_mode:
            #print('\n LOOK AT ME \n')
            return conflicts, can_props
        else:
            # print('\n LOOK AT ME \n')
            return conflicts, can_props, log_test_result, clause_logic_list, unmatched_components  
        
def check_model_for_conflicts(model, candidate_props):
    conflicts = []
    for clause in model.clauses:
       new_conflicts, candidate_props  = logical_test(clause, candidate_props)
       #print('Candidate_props are: ', candidate_props)
       #print('Identified conflicts are: ', new_conflicts)
       #print('there is a new conflict: ')
       #print(new_conflicts)
       if new_conflicts:
           conflicts.append(new_conflicts)
        
    return conflicts, candidate_props

'''
Functions for kernel generation and processing
'''
# function to invert a conflict set into set of diagnoses
def return_diagnoses(conflicts):
    diagnoses = set()
    # (1) Identify components in conflicts
    conflict_components = get_components(conflicts)
    component_mode_dict = {}
    # (2) Identify component modes in conflicts
    for component in conflict_components:
        component_mode_dict[component] = []
        for conflict in conflicts:
            if conflict.component == component:
                component_mode_dict[component].append(conflict.mode)
    # (3) Identify maximum value mode not present in conflicts for each component
        diagnoses_to_add = component.get_remaining_propositions(component_mode_dict[component])
        for diagnosis in diagnoses_to_add:
            diagnoses.add(diagnosis) 
    return diagnoses

def update_kernel_diagnoses(kernel_diagnoses, conflicts):
    # create output variable
    output_kernel_diagnoses = []
   
    # Convert the conflict set (A and B and...) to a set of candidate_diagnoses (not A or not B or...) (application of DeMorgan's Theorem)
    candidate_diagnoses = return_diagnoses(conflicts)
    
    # 0. Check to see if kernel_diagnoses is empty, if so add each element of candidate_diagnoses to the output
    if len(kernel_diagnoses) == 0:
        for elem in candidate_diagnoses:
            output_kernel_diagnoses.append(set([elem]))
        
    else:
    # 1. For all kernels in kernel_diagnoses, check to see if is a subset of candidate_diagnoses.
        # If it is, then remove it from the diagnoses, remove it from conflict, and add it to the output
        # Removal is necessary so don't form supersets in step #2
        elim_list = []
        for kernel in kernel_diagnoses:
            if kernel.issubset(candidate_diagnoses):
                elim_list.append(kernel)    # Track for removal from the diagnoses set
                for elem in kernel:
                    candidate_diagnoses.remove(elem)
                output_kernel_diagnoses.append(kernel)
        
        for kernel in elim_list:
            kernel_diagnoses.remove(kernel)
        
    #2. Add remaining elements in conflict to the remaining kernels in dummy_kernel_diagnoses to form new kernels
        for rem_elem in candidate_diagnoses:
            for rem_kernel in kernel_diagnoses:
                    # remove rem_kernal from the diagnoses and add item to it
                    addition = set()
                    addition.add(rem_elem)
                    for elem in rem_kernel:
                        addition.add(elem)
                    output_kernel_diagnoses.append(addition)
    return output_kernel_diagnoses

def all_kernel_diagnoses(conflicts):
    # Simply call the update_kernel_diagnoses functions on all conflict sets within conflicts
    # and update the diagnoses each time.
    kernel_diagnoses = []
    for conflict in conflicts:
        kernel_diagnoses = update_kernel_diagnoses(kernel_diagnoses, conflict)
    return kernel_diagnoses

def find_highest_probability_diagnosis_set(kernels):
    max_prob = 0
    for kernel in kernels:
        diagnosis = return_diagnoses(kernel)
        diagnosis_prob = 1
        for prop in diagnosis:
            diagnosis_prob *= prop.prob
        if diagnosis_prob > max_prob:
            corr_kernel = kernel
            max_diagnosis = diagnosis
            max_prob = diagnosis_prob
    return max_diagnosis, corr_kernel


'''
Functions specific to our hardware system
'''
# Function to build AND gate clauses
def build_PCU_gate_clause(input_components, AND_gate_component, output_component):
    clauses = set()
    
    #######################################################################
    # This section corresponds do a generic AND gate
    #######################################################################
    
    # Get the necessary propositions for the AND gate component
    not_AND_gate_prop = Proposition(AND_gate_component.name, 0, AND_gate_component)
    AND_gate_prop = Proposition(AND_gate_component.name, 1, AND_gate_component)
    # Get necessary props for the output comopnent
    not_output_prop = Proposition(output_component.name, 0, output_component)
    output_prop = Proposition(output_component.name, 1, output_component)
    # Get the necessary propositions for the input components
    not_input_props = []
    input_props = []
    for component in input_components:
        not_input_props.append(Proposition(component.name, 0, component))
        input_props.append(Proposition(component.name, 1, component))
    # Build out the clauses
    clause_name_start = AND_gate_component.name
    char_num = ord('a')
    for prop in input_props:
        clause_name = clause_name_start + chr(char_num)
        clauses.add(Clause(clause_name,set([not_AND_gate_prop,not_output_prop,prop])))
        char_num += 1
    clause_list = [not_AND_gate_prop, output_prop]
    for prop in not_input_props:
        clause_list.append(prop)
    clause_name = clause_name_start + chr(char_num)
    char_num += 1
    clauses.add(Clause(clause_name,set(clause_list)))
    
    #######################################################################
    # This section adds the clause unique to our PCU behavior
    #######################################################################
    clause_list = [AND_gate_prop, not_output_prop]
    for prop in input_props:
        clause_list.append(prop)
    clause_name = clause_name_start + chr(char_num)
    char_num += 1
    clauses.add(Clause(clause_name,set(clause_list)))
    return clauses
    
def build_Power_Relay_clauses(input_component, power_relay, output_component):
    clauses = set()
    
    # Get the necessary propositions for the power relay component
    not_P_gate_prop = Proposition(power_relay.name, 0, power_relay)
    P_gate_prop = Proposition(power_relay.name, 1, power_relay)
    # Get necessary props for the output
    not_output_prop = Proposition(output_component.name, 0, output_component)
    output_prop = Proposition(output_component.name, 1, output_component)
    # Get the necessary props for the input
    not_input_prop = Proposition(input_component.name, 0, input_component)
    input_prop = Proposition(input_component.name, 1, input_component)
    # Get the necessary propositions for the input components
    clause_name_start = power_relay.name
    char_num = ord('a')
    clause_name = clause_name_start + chr(char_num)
    char_num += 1
    
    #######################################################################
    # This section corresponds to a generic input / output
    #######################################################################
   
    # Add the first clause (not_P OR not_out OR in)
    clauses.add(Clause(clause_name, set([not_P_gate_prop, not_output_prop, input_prop])))
    clause_name = clause_name_start + chr(char_num)
    char_num += 1
    # Add the second clause (not_P OR not_in OR out)
    clauses.add(Clause(clause_name, set([not_P_gate_prop, not_input_prop, output_prop])))
    clause_name = clause_name_start + chr(char_num)
    char_num += 1
    
    #######################################################################
    # This section is unique to the behavior of our power relays
    #######################################################################
    
    # Add thdethird clause (P OR not_out)
    clauses.add(Clause(clause_name, set([P_gate_prop, not_output_prop])))
    return clauses

def build_Camera_clauses(input_component, camera, output_component):
    clauses = set()
    
    # Get the necessary propositions for the power relay component
    not_camera_prop = Proposition(camera.name, 0, camera)
    #camera_prop = Proposition(camera.name, 1, camera)
    # Get necessary props for the output
    not_output_prop = Proposition(output_component.name, 0, output_component)
    output_prop = Proposition(output_component.name, 1, output_component)
    # Get the necessary props for the input
    not_input_prop = Proposition(input_component.name, 0, input_component)
    input_prop = Proposition(input_component.name, 1, input_component)
    # Get the necessary propositions for the input components
    clause_name_start = camera.name
    char_num = ord('a')
    clause_name = clause_name_start + chr(char_num)
    char_num += 1
    
    #######################################################################
    # This section corresponds to a generic input / output
    #######################################################################
   
    # Add the first clause (not_P OR not_out OR in)
    clauses.add(Clause(clause_name, set([not_camera_prop, not_output_prop, input_prop])))
    clause_name = clause_name_start + chr(char_num)
    char_num += 1
    # Add the second clause (not_P OR not_in OR out)
    clauses.add(Clause(clause_name, set([not_camera_prop, not_input_prop, output_prop])))
    clause_name = clause_name_start + chr(char_num)
    char_num += 1
    return clauses




'''
Attempt to build a simple model and conflict directed A*
'''
# Define components
P1 = Component('P1',(0,1),(0.015,0.985), True)
P2 = Component('P2',(0,1),(0.015,0.985), True)
P3 = Component('P3',(0,1),(0.015,0.985), True)

PCU1 = Component('PCU1',(0,1),(0.03,0.97), True)
PCU2 = Component('PCU2',(0,1),(0.03, 0.97), True)

C1 = Component('C1',(0,1),(0.025,0.975), True)
C2 = Component('C2',(0,1),(0.025,0.975), True)

# Define inputs, outputs, intermediate variables -- probability always one b/c value determined by component behavior and other int. variables
    # Inputs
A = Component('A',(1,),(1,), False)
B = Component('B',(1,),(1,), False)
C = Component('C',(1,),(1,), False)

    # Intermediate variables -- these variables have a multivariate domain but are not "assignable" in the sense that their values are determiend by hardware component behavior and the associated propositional logic
V = Component('V',(0,1),(1,1), False)
W = Component('W',(0,1),(1,1), False)
X = Component('X',(0,1),(1,1), False)

Y = Component('Y',(0,1),(1,1), False)
Z = Component('Z',(0,1),(1,1), False)

    # Outputs
D = Component('D',(0,),(1,), False)
E = Component('E',(1,),(1,), False)

# Use our functions to build our model

testP1 = build_Power_Relay_clauses(A, P1, V)

testP2 = build_Power_Relay_clauses(B, P2, W)

testP3 = build_Power_Relay_clauses(C, P3, X)

testPCU1 = build_PCU_gate_clause([V,W],PCU1, Y)

testPCU2 = build_PCU_gate_clause([W,X],PCU2, Z)

testC1 = build_Camera_clauses(Y,C1,D)

testC2 = build_Camera_clauses(Z,C2,E)

'''
Define simplified problem where V and W values are known
'''
V = Component('V',(1,),(1,), False)
W = Component('W',(1,),(1,), False)
D = Component('D',(0,),(1,), False)


# PCU1 propositions and clauses
props = [Proposition('PCU1',0, PCU1), Proposition('Y', 0, Y), Proposition('V', 1, V)]
PCU1a = Clause('PCU1a',set(props))

props = [Proposition('PCU1',0, PCU1), Proposition('Y', 0, Y), Proposition('W', 1, W)]
PCU1b = Clause('PCU1b',set(props))

props = [Proposition('PCU1',0, PCU1), Proposition('V', 0, V), Proposition('W', 0, W),Proposition('Y', 1, Y)]
PCU1c = Clause('PCU1c',set(props))

props = [Proposition('PCU1', 1, PCU1), Proposition('Y', 0, Y) , Proposition('V', 1, V), Proposition('W', 1, W)]
PCU1d = Clause('PCU1d',set(props))

PCU1_clauses = set([PCU1a, PCU1b, PCU1c, PCU1d])

# C1 propositions and clauses
props = [Proposition('C1',0, C1), Proposition('Y', 0, Y), Proposition('D', 1, D)]
C1a = Clause('C1a', set(props))

props = [Proposition('C1',0, C1), Proposition('D', 0, D), Proposition('Y', 1, Y)]
C1b = Clause('C1b', set(props))

C1_clauses = set([C1a, C1b])

# Combine all clauses into a model
all_clauses = set.union(PCU1_clauses, C1_clauses)

simple_model = Model(all_clauses)

# Try out candidate propositions
candidate_props = set([Proposition('PCU1', 1, PCU1), Proposition('W', 1, W), Proposition('V', 1, V), Proposition('C1', 1, C1), Proposition('D', 0, D)])
for prop in candidate_props:
    prop.support = 'Given'

test = generate_exhaustive_proposition_sets(simple_model, candidate_props)

print(test)

# conflicts, candidate_props = check_model_for_conflicts(simple_model, candidate_props)

# print(conflicts)

'''
Need to update the return_diagnosis function to:
    - select the highest probability value from the component that excludes the conflict
    - deal with our Classes
'''
# output_kernels = all_kernel_diagnoses(conflicts)
# #print(output_kernels)

# best_diagnosis, corr_kernel = find_highest_probability_diagnosis_set(output_kernels)
#print(best_diagnosis)

def update_candidate_props(candidate_props, diagnosis):
    props_to_remove = []
    for prop in candidate_props:
        for diag_prop in diagnosis:
            if prop.component == diag_prop.component:
                props_to_remove.append(prop)
    for diag_prop in diagnosis:
        diag_prop.support = 'kernel'
        candidate_props.add(diag_prop)
    for prop in props_to_remove:
       candidate_props.remove(prop)
    return candidate_props

# update_candidate_props(candidate_props, best_diagnosis)
# #print('updated candidate props are: ', candidate_props)

# conflicts, candidate_props = check_model_for_conflicts(simple_model, candidate_props)
# print('conflicts after applying kernel are: ', conflicts)

def return_consistent_configurations(model, known_inputs, known_outputs, N):
    # Initialize
    used_kernels = []
    consistent_configs = []
    config_likelihoods = []
    # (1) Start with highest probability component configurations
    candidate_props = set()
    for prop in known_inputs:
        candidate_props.add(prop)
    for prop in known_outputs:
        candidate_props.add(prop)
    for component in model.components:
        candidate_props.add(component.get_max_proposition())
    # (2) Find satisfiable configurations until either (a) kernels exhausted or (b) find N solutions
    # (2) Check initial configuratin for conflicts
    conflicts = check_model_for_conflicts(model, candidate_props)
    count = 0
    still_kernels = True
    if conflicts:
        while still_kernels and (count < N):
            # Get kernels from the conflicts
            output_kernels = all_kernel_diagnoses(conflicts)
            # Get the best diagnosis from the kernel set
            best_diagnosis, corr_kernel = find_highest_probability_diagnosis_set(output_kernels)
            # Update the used kernels and remove the used kernel from the set
            used_kernels.append(corr_kernel)
            output_kernels.remove(corr_kernel)
            if output_kernels:
                still_kernels = True
            else:
                still_kernels = False
            # Get updated propositions based on the selected kernel
            candidate_props = update_candidate_props(candidate_props, best_diagnosis)
            # Check the new proposition set to see if it induces conflicts
            conflicts = check_model_for_conflicts(model, candidate_props)
            if not conflicts:
                count += 1
                consistent_configs.append(candidate_props)
                config_likelihoods.append(compute_proposition_set_likelihood(candidate_props))
        if conflicts:
            print('WARNING: problem is undiagnosable. You likely have an error in your proposition, clause, or component defintions.')
        else:
            return consistent_configs, config_likelihoods
    else:
        print('The best diagnosis is that all hardware is functioning normally!')
        consistent_configs.append(candidate_props)
        config_likelihoods.append(compute_proposition_set_likelihood(candidate_props))
        return consistent_configs, config_likelihoods


        
    


# if conflicts:
    

# print(conflicts)
# print('\n')
# print(candidate_props)
# print('\n')
# print(support)

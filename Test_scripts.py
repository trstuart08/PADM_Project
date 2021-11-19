# -*- coding: utf-8 -*-
"""
Created on Thu Nov 18 09:43:40 2021

@author: Tom Stuart [thoma]
"""

'''
Test find highest probability proposition function
'''
props = [Proposition('PCU1',1, PCU1), Proposition('P1', 1, P1), Proposition('C1', 1, C1)]
test_result = find_highest_probability_proposition(props)
print(test_result)

props = [Proposition('PCU1',1, PCU1), Proposition('P1', 0, P1), Proposition('C1', 1, C1)]
test_result = find_highest_probability_proposition(props)
print(test_result)

props = [Proposition('PCU1',1, PCU1), Proposition('P1', 0, P1), Proposition('C1', 0, C1)]
test_result = find_highest_probability_proposition(props)
print(test_result)

props = [Proposition('Y',1, Y), Proposition('V', 1, V), Proposition('W', 1, W)]
test_result = find_highest_probability_proposition(props)
print(test_result)

props = [Proposition('Y',1, Y), Proposition('V', 0, V), Proposition('W', 1, W)]
test_result = find_highest_probability_proposition(props)
print(test_result)

props = [Proposition('Y',0, Y), Proposition('V', 0, V), Proposition('W', 1, W)]
test_result = find_highest_probability_proposition(props)
print(test_result)

props = [Proposition('Y',0, Y), Proposition('V', 0, V), Proposition('W', 0, W)]
test_result = find_highest_probability_proposition(props)
print(test_result)
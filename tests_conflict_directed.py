# -*- coding: utf-8 -*-
"""
Created on Sun Nov 14 06:38:27 2021

@author: Tom Stuart [thoma]
"""
vals_to_exclude = []
if not vals_to_exclude:
    print('tests as false')


P1 = Proposition('P1',1)
# print(P1)

P1.change_mode(2)
# print(P1)

# print(P1.logical_test(1))

P2 = Proposition('P2',1)

my_props = set([P1, P2])
# print(my_props)

first_clause = Clause('first_prop', set([P1, P2]))
# print(first_clause)
# print(first_clause.props)


can_props = [Proposition('A1',0)]
print('Testing {(P1,2), (P2,1)} with [(A1,0)]:')
print(first_clause.logical_test(can_props))
print('\n')

can_props = [Proposition('P1',0)]
print('Testing {(P1,2), (P2,1)} with [(P1,0)]:')
print(first_clause.logical_test(can_props))
print('\n')

can_props = [Proposition('P1',0), Proposition('P2',2), Proposition('A1',0)]
print('Testing {(P1,2), (P2,1)} with [(P1,0), (P2, 2), (A1,0)]:')
print(first_clause.logical_test(can_props))
print('\n')

second_clause = Clause('second_prop', set([P1, P2, Proposition('A1',0), Proposition('A2',1)]))
can_props = [Proposition('P1',1), Proposition('P2',0), Proposition('A1',1)]
print('Testing {(P1,2), (P2,1), (A1, 0), (A2, 1)} with [(P1,1), (P2, 0), (A1,1)]:')
print(second_clause.logical_test(can_props))
print('\n')

test_case2 = second_clause.logical_test(can_props)
print('This is the test case 2 return: ')
print(test_case2)
print('\n')
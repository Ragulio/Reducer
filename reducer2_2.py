import unfolded_dictionary as uf

#when hitting a number in a string, it returns the length of the full number
def full_num(f):
    if not f[0].isdigit():
        print('Error! This is not a number.')
        return 0
    if f.isdigit():
        return len(f)
    i=0
    while i < len(f) and f[i].isdigit():
        i+= 1
    return i

#rewrites a formula incrementing all the variable numbers
def inc_variables(formula,increment):
    if formula == '':
        return ''
    new_formula = ''
    i = 0
    while i + 2 < len(formula):
        if formula[i:i+2] == 'v_' and formula[i+2].isdigit():
            j = full_num(formula[i+2:])
            var_num = int(formula[i+2:i+2+j]) + increment
            new_formula+= 'v_' + str(var_num)
            i+= j + 2
        else:
            new_formula+= formula[i]
            i+= 1
    return new_formula + formula[i:]

#returns the list of operands of one operator in a given formula
#only sees the first instance of the operator
def fetch_operands(operator,formula):
    if not formula[-1] == ' ': #safety measure
        formula+= ' '
    if not operator in formula:
        return[]
    i = formula.index(operator)
    i+= len(operator)
    if formula[i] != '{':
        return[]
    i+= 1
    count = 1
    operands = []
    operand = ''
    while count != 0:
        if formula[i] == '}': #by safety measure, no need to check length
            count+= -1
            if count == 0:
                operands.append(operand)
                operand = ''
            else:
                operand+= formula[i]
            i+= 1
            if formula[i] == '{':
                if count > 0:
                    operand+= formula[i]
                count+= 1
                i+= 1
        elif formula[i] == '{':
            if count > 0:
                operand+= formula[i]
            count+= 1
            i+= 1
        else:
            operand+= formula[i]
            i+= 1
    return operands

#returns the name of an operator, stripped of the operands
def operator_name(operator):
    name = ''
    for char in operator:
        if char != '{':
            name+= char
        else:
            break
    return name

#changes names of quantified variables to avoid those in q_var
#also modifies q_var adding the new quantified variables
def unrepeat_quantvar(f,q_var):
    g = f.rstrip() + ' '    #safety measure for a variable in final position
    f_ordered_vars = list(variable_list(f))
    f_ordered_vars.sort()
    if f_ordered_vars == set():
        return f

    #create a temporary variable set, so not to cause overlaps
    g = g.replace ('v_', '!TEMP!')
    for var in f_ordered_vars:
        if '\\forall !TEMP!' + str(var) + ' ' in g:
            i = g.index('\\forall !TEMP!' + str(var) + ' ')
        elif '\\ex {!TEMP!' + str(var) + '}' in g:
            i = g.index('\\ex {!TEMP!' + str(var) + '}')
        elif '\\exuniq {!TEMP!' + str(var) + '}' in g:
            i = g.index('\\exuniq {!TEMP!' + str(var) + '}')
        else:
            continue

        if var in q_var:
            bad_var = '!TEMP!' + str(var)
            new_var = 'v_' + str(max(q_var) + 1)
            g = g[:i] + g[i:].replace(bad_var + ' ', new_var + ' ')
            g = g[:i] + g[i:].replace(bad_var + '}', new_var + '}')
            q_var.add(int(new_var[2:]))
        else:
            q_var.add(var)
    return g.replace('!TEMP!','v_').rstrip()

#reduce the operator inside the formula f
#operands are fed as empty names, but in the output they are the actual ones
def single_reduce_operator(f,operator,reduced,increment=0):
    #first extract the operator name and check it is actually in f
    op_name = operator_name(operator)
    if not op_name in f:
        return f

    #extract the symbolic operands and the actual ones
    symbolic_operands = fetch_operands(op_name,operator)
    actual_operands = fetch_operands(op_name,f)

    #create a dictionary between symbolic and actual operands
    if len(symbolic_operands) != len(actual_operands):
        print('Please check that the number of operands is correct.')
        return None
    else:
        operands = {}
        for i in range(len(symbolic_operands)):
            operands[symbolic_operands[i]] = actual_operands[i]
    del symbolic_operands
    del actual_operands
            
    #reduce, but whenever a symbolic operand appears, we write the
    #actual operand instead
    inc_reduced = inc_variables(reduced,increment)
    i = f.index(op_name)
    g = f[:i]

    #construct a list of quantified variables, so not to quantify more than once
    #only need forall, because f[:i] is already completely reduced
    q_var = set()
    for variable in variable_list(g):
        if '\\forall v_' + str(variable) + ' ' in g:
            q_var.add(variable)
    if op_name in ['\\exuniq ','\\ex ']:
        q_var.add(int(operands['V'][2:]))

    #modify the actual operands, so not to repeat quantified variables
    #but unrepeat_quantvar may change length, so save the old lengths
    inc_reduced = unrepeat_quantvar(inc_reduced,q_var)
    old_operand_lengths = {}
    for sop in operands:
        old_operand_lengths[sop] = len(operands[sop])
        operands[sop] = unrepeat_quantvar(operands[sop],q_var)
        inc_reduced = inc_reduced.replace(sop,operands[sop])
    g+= inc_reduced

    #write the rest of the formula
    i+= len(op_name)
    for sop in operands:
        i+= old_operand_lengths[sop] + 2
    g+= unrepeat_quantvar(f[i:],q_var)
    return g

#returns whether or not the formula f is elementary, meaning it only has the
#basic symbols plus free variables, which may not contain \\
def is_elementary(f):
    words = f.split()
    i = 0
    while i < len(words):
        if words[i] in ['\\neg','\\vee','\\forall','\\in']:
            i+= 1
        elif len(words[i]) > 2 and words[i][:2] == 'v_' and words[i][2:].isdigit():
            i+= 1
        elif '\\' not in words[i]:
            i+= 1
        else:
            return False
    return True

#counts the distinct variables contained in the formula f
def variable_list(f):
    if f == '':
        return set()
    variables = set()
    i = 0
    while i < len(f):
        if i+3 <= len(f) and f[i:i+2] == 'v_' and f[i+2].isdigit():
            j = full_num(f[i+2:])
            variable = int(f[i+2:i+j+2])
            if variable not in variables:
                variables.add(variable)
            i+= j+2
        else:
            i+= 1
    return variables

#resturns the first name in the list to be found in the formula
def first_hit(formula,names):
    first_hits = {}
    for name in names:
        if name in formula:
            name_hit = formula.index(name)
            first_hits[name_hit] = name
    the_first = min(first_hits.keys())
    return first_hits[the_first]

#creates a dictionary with all known operators or statements
def create_dictionary():
    k = {}
    k['\\ex {V}'] = '\\neg \\forall V \\neg'
    k['\\exuniq {V}{P}'] = 'NEED SPECIAL FUNCTION.'
    k['\\wedge {P1}{P2}'] = '\\neg \\vee \\neg P1 \\neg P2'
    k['\\wedge3 {P1}{P2}{P3}'] = '\\wedge {\\wedge {P1}{P2}}{P3}'
    k['\\wedge4 {P1}{P2}{P3}{P4}'] = '\\wedge {\\wedge {\\wedge {P1}{P2}}{P3}}{P4}'
    k['\\wedge5 {P1}{P2}{P3}{P4}{P5}'] = '\\wedge {\\wedge {\\wedge {\\wedge {P1}{P2}}{P3}}{P4}}{P5}'
    k['\\wedge6 {P1}{P2}{P3}{P4}{P5}{P6}'] = '\\wedge {\\wedge {\\wedge {\\wedge {\\wedge {P1}{P2}}{P3}}{P4}}{P5}}{P6}'
    k['\\emptyset {V}'] = '\\forall v_0 \\neg \\in v_0 V'
    k['\\containempty {V}'] = '\\ex {v_0} \\wedge {\\emptyset {v_0}}{\\in v_0 V}'
    k['\\imply {P1}{P2}'] = '\\vee \\neg P1 P2'
    k['\\coimply {P1}{P2}'] = '\\wedge {\\imply {P1}{P2}}{\\imply {P2}{P1}}'
    k['\\equal {V1}{V2}'] = '\\forall v_0 \\coimply {\\in v_0 V1}{\\in v_0 V2}'
    k['\\insuccessor {V1}{V2}'] = '\\vee \\in V1 V2 \\equal {V1}{V2}'
    k['\\successor {V1}{V2}'] = '\\forall v_0 \\coimply {\\in v_0 V1}{\\insuccessor {v_0}{V2}}'
    k['\\singleton {V1}{V2}'] = '\\forall v_0 \\coimply {\\in v_0 V1}{\\equal {v_0}{V2}}'
    k['\\couple {V1}{V2}{V3}'] = '\\forall v_0 \\coimply {\\in v_0 V1}{\\vee \\equal {v_0}{V2} \\singleton {v_0}{V3}}'
    k['\\couplin {V1}{V2}{V3}'] = '\\ex {v_0} \\wedge {\\couple {v_0}{V1}{V2}}{\\in v_0 V3}'
    k['\\transitive {V}'] = '\\forall v_0 \\imply {\\in v_0 V}{\\ex {v_1} \\wedge {\\successor {v_1}{v_0}}{\\in v_1 V}}'
    k['\\subseteq {V1}{V2}'] = '\\forall v_0 \imply {\\in v_0 V1}{\\in v_0 V2}'
    k['\\isnaturals {V}'] = '\\wedge3 {\\containempty {V}}{\\transitive {V}}{\\forall v_0 \\imply {\\wedge {\\containempty {v_0}}{\\transitive {v_0}}}{\\subseteq {V}{v_0}}}'
    k['\\relation {V1}{V2}{V3}'] = '\\forall v_0 \\coimply {\\in v_0 V1}{\\ex {v_1} \\ex {v_2} \\wedge3 {\\in v_1 V2}{\\in v_2 V3}{\\couple {v_0}{v_1}{v_2}}}'
    k['\\function {F}{X}{Y}'] = '\\wedge {\\relation {F}{X}{Y}}{\\forall v_0 \\imply {\\in v_0 X}{\\exuniq {v_1}{\\wedge {\\in v_1 Y}{\\couplin {v_0}{v_1}{F}}}}}'
    k['\\isintzero {V}'] = '\\forall v_0 \\coimply {\\in v_0 V}{\\ex {v_1} \\ex {v_2} \\ex {v_3} \\wedge4 {\\isnaturals {v_1}}{\\in v_2 v_1}{\\equal {v_2}{v_3}}{\\couple {v_0}{v_2}{v_3}}}'
    k['\\sequence {F}{X}'] = '\\ex {v_0} \\wedge {\\isnaturals {v_0}}{\\function {F}{v_0}{X}}'
    k['\\product {V1}{V2}{V3}'] = '\\forall v_0 \\coimply {\\in v_0 V1}{\\ex {v_1} \\ex {v_2} \\wedge3 {\\in v_1 V2}{\\in v_2 V3}{\\couple {v_0}{v_1}{v_2}}}'
    k['\\binop {F}{X}'] = '\\ex {v_0} \\wedge {\\product {v_0}{X}{X}}{\\function {F}{v_0}{X}}'
    k['\\natbinop {F}'] = '\\ex {v_0} \\wedge {\\isnaturals {v_0}}{\\binop {F}{v_0}}'
    k['\\triplin {V1}{V2}{V3}{V4}'] = '\\ex {v_0} \\ex {v_1} \\wedge3 {\\couple {v_0}{V1}{V2}}{\\couple {v_1}{v_0}{V3}}{\\in v_1 V4}'
    k['\\isnataddition {F}'] = '\\wedge {\\natbinop {F}}{\\forall v_0 \\forall v_1 \\forall v_2 \\imply {\\triplin {v_0}{v_1}{v_2}{F}}{\\wedge {\\imply {\\emptyset {v_1}}{\\equal {v_0}{v_2}}}{\\ex {v_3} \\ex {v_4} \\wedge3 {\\successor {v_3}{v_1}}{\\successor {v_4}{v_2}}{\\triplin {v_0}{v_3}{v_4}{F}}}}}'
    k['\\naturalsum {V1}{V2}{V3}'] = '\\ex {v_0} \\wedge {\\isnataddition {v_0}}{\\triplin {V1}{V2}{V3}{v_0}}'
    k['\\isnatmultipl {F}'] = '\\wedge {\\natbinop {F}}{\\forall v_0 \\forall v_1 \\forall v_2 \\imply {\\triplin {v_0}{v_1}{v_2}{F}}{\\wedge {\\imply {\\emptyset {v_1}}{\\emptyset {v_2}}}{\\ex {v_3} \\ex {v_4} \\ex {v_5} \\wedge3 {\\successor {v_3}{v_1}}{\\naturalsum {v_2}{v_0}{v_4}}{\\triplin {v_0}{v_3}{v_4}{F}}}}}'
    k['\\integer {V}'] = '\\ex {v_0} \\ex {v_1} \\ex {v_2} \\wedge4 {\\isnaturals {v_0}}{\\in v_1 v_0}{\\in v_2 v_0}{\\forall v_3 \\coimply {\\in v_3 V}{\\ex {v_4} \\ex {v_5} \\ex {v_6} \\wedge6 {\\in v_4 v_0}{\\in v_5 v_0}{\\in v_6 v_0}{\\couple {v_3}{v_4}{v_5}}{\\naturalsum {v_1}{v_5}{v_6}}{\\naturalsum {v_4}{v_2}{v_6}}}}'
    k['\\isintegers {X}'] = '\\forall v_0 \\coimply {\\in v_0 X}{\\integer {v_0}}'
    k['\\integersum {V1}{V2}{V3}'] = '\\forall v_0 \\forall v_1 \\imply {\\couplin {v_0}{v_1}{V3}}{\\forall v_2 \\forall v_3 \\forall v_4 \\forall v_5 \\imply {\\wedge {\\couplin {v_2}{v_3}{V1}}{\\couplin {v_4}{v_5}{V2}}}{\\ex {v_6} \\ex {v_7} \\ex {v_8} \\ex {v_9} \\ex {v_10} \\wedge6 {\\isnataddition {v_6}}{\\triplin {v_2}{v_4}{v_7}{v_6}}{\\triplin {v_7}{v_1}{v_8}{v_6}}{\\triplin {v_3}{v_5}{v_9}{v_6}}{\\triplin {v_9}{v_0}{v_10}{v_6}}{\\equal {v_8}{v_10}}}}'
    k['\\integerproduct {V1}{V2}{V3}'] = '\\forall v_0 \\forall v_1 \\imply {\\couplin {v_0}{v_1}{V3}}{\\forall v_2 \\forall v_3 \\forall v_4 \\forall v_5 \\imply {\\wedge {\\couplin {v_2}{v_3}{V1}}{\\couplin {v_4}{v_5}{V2}}}{\\ex {v_6} \\ex {v_7} \\ex {v_8} \\ex {v_9} \\ex {v_10} \\ex {v_11} \\ex {v_12} \\ex {v_13} \\ex {v_14} \\wedge4 {\\wedge {\\isnataddition {v_6}}{\\isnatmultipl {v_7}}}{\\wedge4 {\\triplin {v_2}{v_4}{v_8}{v_7}}{\\triplin {v_3}{v_5}{v_9}{v_7}}{\\triplin {v_8}{v_9}{v_10}{v_6}}{\\triplin {v_10}{v_1}{v_11}{v_6}}}{\\wedge4 {\\triplin {v_2}{v_5}{v_12}{v_7}}{\\triplin {v_3}{v_4}{v_13}{v_7}}{\\triplin {v_12}{v_13}{v_14}{v_6}}{\\triplin {v_14}{v_0}{v_15}{v_6}}}{\\equal {v_11}{v_15}}}}'
    k['\\intsmaller {V1}{V2}'] = '\\forall v_0 \\forall v_1 \\forall v_2 \\forall v_3 \\imply {\\wedge {\\couplin {v_0}{v_1}{V1}}{\\couplin {v_2}{v_3}{V2}}}{\\forall v_4 \\forall v_5 \\forall v_6 \\imply {\\wedge3 {\\isnataddition {v_4}}{\\triplin {v_0}{v_3}{v_5}{v_4}}{\\triplin {v_2}{v_1}{v_6}{v_4}}}{\\in v_5 v_6}}'
    k['\\rational {V}'] = '\\ex {v_0} \\ex {v_1} \\ex {v_2} \\wedge4 {\\isintegers {v_0}}{\\in v_1 v_0}{\\in v_2 v_0}{\\forall v_3 \\coimply {\\in v_3 V}{\\ex {v_4} \\ex {v_5} \\ex {v_6} \\wedge4 {\\in v_4 v_0}{\\in v_5 v_0}{\\in v_6 v_0}{\\wedge4 {\\couple {v_3}{v_4}{v_5}}{\\neg \\emptyset {v_5}}{\\integerproduct {v_1}{v_5}{v_6}}{\\integerproduct {v_4}{v_2}{v_6}}}}}'
    k['\\isrationals {X}'] = '\\forall v_0 \\coimply {\\in v_0 X}{\\rational {v_0}}'
    k['\\ratseq {F}'] = '\\ex {v_0} \\ex {v_1} \\wedge3 {\\isnaturals {v_0}}{\\isrationals {v_1}}{\\function {F}{v_0}{v_1}}'
    k['\\rationalsum {V1}{V2}{V3}'] = '\\forall v_0 \\forall v_1 \\imply {\\couplin {v_0}{v_1}{V3}}{\\forall v_2 \\forall v_3 \\forall v_4 \\forall v_5 \\imply {\\wedge {\\couplin {v_2}{v_3}{V1}}{\\couplin {v_4}{v_5}{V2}}}{\\ex {v_6} \\ex {v_7} \\ex {v_8} \\ex {v_9} \\ex {v_10} \\ex {v_11} \\ex {v_12} \\wedge3 {\\wedge5 {\\integerproduct {v_2}{v_5}{v_6}}{\\integerproduct {v_6}{v_1}{v_7}}{\\integerproduct {v_4}{v_3}{v_8}}{\\integerproduct {v_8}{v_1}{v_9}}{\\integersum {v_7}{v_9}{v_10}}}{\\wedge {\\integerproduct {v_3}{v_5}{v_11}}{\\integerproduct {v_11}{v_0}{v_12}}}{\\equal {v_10}{v_12}}}}'
    k['\\rationalproduct {V1}{V2}{V3}'] = '\\forall v_0 \\forall v_1 \\imply {\\couplin {v_0}{v_1}{V3}}{\\forall v_2 \\forall v_3 \\forall v_4 \\forall v_5 \\imply {\\wedge {\\couplin {v_2}{v_3}{V1}}{\\couplin {v_4}{v_5}{V2}}}{\\ex {v_6} \\ex {v_7} \\ex {v_8} \\ex {v_9} \\wedge5 {\\integerproduct {v_2}{v_4}{v_6}}{\\integerproduct {v_6}{v_1}{v_7}}{\\integerproduct {v_3}{v_5}{v_8}}{\\integerproduct {v_8}{v_0}{v_9}}{\\equal {v_7}{v_9}}}}'
    k['\\ratsmaller {V1}{V2}'] = '\\forall v_0 \\forall v_1 \\forall v_2 \\forall v_3 \\forall v_4 \\imply {\\wedge5 {\\isintzero {v_0}}{\\couplin {v_1}{v_2}{V1}}{\\couplin {v_3}{v_4}{V2}}{\\intsmaller {v_0}{v_2}}{\\intsmaller {v_0}{v_4}}}{\\forall v_5 \\forall v_6 \\imply {\\wedge {\\integerproduct {v_1}{v_4}{v_5}}{\\integerproduct {v_2}{v_3}{v_6}}}{\\intsmaller {v_5}{v_6}}}'
    k['\\ratdiffsmaller {V1}{V2}{V3}'] = '\\forall v_0 \\wedge {\\imply {\\wedge {\\ratsmaller {V1}{V2}}{\\rationalsum {V1}{V3}{v_0}}}{\\ratsmaller {V2}{v_0}}}{\\imply {\\wedge {\\ratsmaller {V2}{V1}}{\\rationalsum {V2}{V3}{v_0}}}{\\ratsmaller {V1}{v_0}}}'
    k['\\cauchyseq {F}'] = '\\ex {v_0} \\ex {v_1} \\wedge4 {\\isnaturals {v_0}}{\\isrationals {v_1}}{\\function {F}{v_0}{v_1}}{\\forall v_2 \\imply {\\in v_2 v_1}{\\ex {v_3} \\wedge {\\in v_3 v_0}{\\forall v_4 \\forall v_5 \\imply {\\wedge4 {\\in v_4 v_0}{\\in v_5 v_0}{\\in v_3 v_4}{\\in v_3 v_5}}{\\forall v_6 \\forall v_7 \\imply {\\wedge {\\couplin {v_4}{v_6}{F}}{\\couplin {v_5}{v_7}{F}}}{\\ratdiffsmaller {v_6}{v_7}{v_3}}}}}}'
    k['\\real {V}'] = '\\wedge {\\forall v_0 \\imply {\\in v_0 V}{\\cauchyseq {v_0}}}{\\ex {v_1} \\wedge {\\in v_1 x}{\\forall v_2 \\forall v_3 \\imply {\\wedge {\\in v_2 V}{\\rational {v_3}}}{\\ex {v_4} \\ex {v_5} \\wedge3 {\\isnaturals {v_4}}{\\in v_5 v_4}{\\forall v_6 \\imply {\\wedge {\\in v_6 v_4}{\\in v_5 v_6}}{\\ex {v_7} \\ex {v_8} \\wedge3 {\\couplin {v_6}{v_7}{V}}{\\couplin {v_6}{v_8}{v_1}}{\\ratdiffsmaller {v_7}{v_8}{v_3}}}}}}}'
    k['\\isreals {X}'] = '\\forall v_0 \\coimply {\\in v_0 X}{\\real {v_0}}'
    k_names = {}
    for operator in k.keys():
        k_names[operator_name(operator)] = operator
    return [k,k_names]

#reduces a formula, performing all the reductions contained in k
#slov is optional, if 1 it selects the already trained dictionary
def reduction(f,slov=0):
    g = f
    k,k_names = create_dictionary()
    if slov != 0:
        k_unfolded = uf.create_unfolded_dictionary()
    while not is_elementary(g):
        next_unreduced = first_hit(g,k_names.keys())
        unreduced = k_names[next_unreduced]
        
        if next_unreduced == '\\exuniq ':
            #construct a list of quantified variables
            q_var = set()
            i = g.index('\\exuniq ')

            #those before our \\exuniq operator
            for variable in variable_list(g[:i]):
                if '\\forall v_' + str(variable) + ' ' in g[:i]:
                    q_var.add(variable)
            [V,P] = fetch_operands('\\exuniq ',g)

            #the one we are quantifying just now
            q_var.add(int(V[2:])) #because var has the form v_n

            #those in prop, all of which appears before the new variable
            for variable in variable_list(P):
                q_var.add(variable)

            #we can finally construct the new variable
            new_V = 'v_' + str(max(q_var) + 1)
            P+= ' '
            new_P = P.replace(V + ' ',new_V + ' ')
            new_P = new_P.replace (V + '}',new_V + '}')
            new_P = new_P.strip()
            reduced = '\\wedge {\\ex {V} P}{\\forall '+new_V+' \\imply {'
            reduced+= new_P + '}{\\equal {' + new_V + '}{V}}}'
            g = single_reduce_operator(g,unreduced,reduced)
        elif slov !=0 and unreduced in k_unfolded:
            reduced = k_unfolded[unreduced]
            g = single_reduce_operator(g,unreduced,reduced)
        else:
            reduced = k[unreduced]
            g = single_reduce_operator(g,unreduced,reduced)
    return g

#checks that in a reduced formula f the quantified variables are consistent
#i.e. they are ordered, don't skip, don't repeat and respect axiom of regularity
def check_q(f):
    g = f
    q_vars = []
    for var in variable_list(g):
        if '\\in v_' + str(var) + ' v_' + str(var) + ' ' in g:
            print(var)
            return False
    while '\\forall v_' in g:
        i = g.index('\\forall v_')
        g = g[i+10:]
        current_var = int(g[:full_num(g)])
        if current_var in q_vars:
            print(current_var)
            return False
        if not q_vars and current_var:
            print(current_var)
            return False
        if q_vars and current_var != max(q_vars) + 1:
            print(current_var)
            return False
        q_vars.append(current_var)
    return True


#gives a full LaTeX reduction of f, adding curly brackets to subscript numbers
def lr(f,check=False):
    g = reduction(f) + ' '
    if check:
        print(check_q(g))
    for variable in variable_list(g):
        g = g.replace('v_'+str(variable)+' ','v_{'+str(variable)+'} ')
    print(g.strip())

#it trains the dictionary with the fully unraveled formulas already known
def train_dict(trigger = None):
    a = input('This might take some time. Are you sure you want to proceed? y/n\n')
    if a != 'y':
        return
    filename = 'unfolded_dictionary.py'
    try:
        k = create_unfolded_dictionary()
    except NameError:
        k = {}
    new_k,new_k_names = create_dictionary()
    with open(filename,'w') as slov:
        slov.write("def create_unfolded_dictionary():")
        slov.write("\n\tk = {}")
        for key,value in new_k.items():
            if '\\ex' not in key and '\\wedge' not in key and 'imply ' not in key:
                if key not in k:
                    new_key = r"{}".format(key).replace('\\','\\\\')
                    new_value = r"{}".format(reduction(key)).replace('\\','\\\\')
                    entry = '\n\t' + f"k['{new_key}'] = '{new_value}'"
                    slov.write(entry)

        slov.write("\n\treturn k")


    


def reduction_debug(f):
    g = f
    [k,k_names] = create_dictionary()
    next_unreduced = first_hit(g,k_names.keys())
    unreduced = k_names[next_unreduced]
    if next_unreduced == '\\exuniq ':
        #construct a list of quantified variables
        q_var = []
        i = g.index('\\exuniq ')

        #those before our \\exuniq operator
        for variable in variable_list(g[:i]):
            if '\\forall v_' + str(variable) + ' ' in g[:i]:
                q_var.add(variable)
        [var,prop] = fetch_operands('\\exuniq ',g)

        #the one we are quantifying just now
        q_var.add(int(var[2:])) #because var has the form v_n

        #those in prop, all of which appears before the new variable
        for variable in variable_list(prop):
            q_var.add(variable)

        #we can finally construct the new variable
        new_var = 'v_' + str(max(q_var) + 1)
        prop+= ' '
        new_prop = prop.replace(var + ' ',new_var + ' ')
        new_prop = new_prop.replace (var + '}',new_var + '}')
        new_prop = new_prop.strip()
        reduced = '\\wedge {\\ex {var}{prop}}{\\forall '+new_var+' \\imply {'
        reduced+= new_prop + '}{\\equal {' + new_var + '}{var}}}'
        print(reduced)
        g = single_reduce_operator(g,unreduced,reduced)
    else:
        reduced = k[unreduced]
        g = single_reduce_operator(g,unreduced,reduced)
    return g

def is_elementary_debug(f):
    words = f.split()
    i = 0
    while i < len(words):
        if words[i] in ['\\neg','\\vee','\\forall','\\in']:
            i+= 1
        elif len(words[i]) > 2 and words[i][:2] == 'v_' and words[i][2:].isdigit():
            i+= 1
        elif '\\' not in words[i]:
            i+= 1
        else:
            j = f.index(words[i])
            print(f[j:])
            return False
    return True

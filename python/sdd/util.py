import sdd

def global_model_count(alpha,manager):
    mc = sdd.sdd_model_count(alpha,manager)
    var_count = sdd.sdd_manager_var_count(manager)
    var_used = sdd.sdd_variables(alpha,manager)
    for used in var_used[1:]:
        if not used:
            mc = 2*mc
    return mc

def sdd_exactly_one_among(manager, active_variables, background_variables):
    if not all(x in background_variables for x in active_variables):
        raise Exception("Invalid argument active variables %s, background_variables %s " % (active_variables, background_variables) )
    result = sdd.sdd_manager_false(manager)
    for positive_variable in active_variables:
        cur_term = sdd.sdd_manager_true(manager)
        for variable in background_variables:
            if variable != positive_variable:
                cur_lit = sdd.sdd_manager_literal(-variable, manager)
            else:
                cur_lit = sdd.sdd_manager_literal(variable, manager)
            cur_term = sdd.sdd_conjoin(cur_term, cur_lit, manager)
        sdd.sdd_save("t1.sdd", result)
        sdd.sdd_save("t2.sdd", cur_term)
        sdd.sdd_vtree_save("manager.vtree", sdd.sdd_manager_vtree(manager))
        result = sdd.sdd_disjoin(result, cur_term, manager)
    return result

def sdd_exactly_one(manager, variables):
    return sdd_exactly_one_among(manager, variables, variables)

def sdd_negative_term(manager, variables):
    result = sdd.sdd_manager_true(manager)
    for variable in variables:
        result = sdd.sdd_conjoin(result, sdd.sdd_manager_literal(-variable, manager), manager)
    return result

def sdd_term(manager, variables, positive_variable):
    result = sdd.sdd_manager_true(manager)
    for variable in variables:
        if variable in positive_variable:
            result = sdd.sdd_conjoin(result, sdd.sdd_manager_literal(variable, manager), manager)
        else:
            result = sdd.sdd_conjoin(result, sdd.sdd_manager_literal(-variable, manager), manager)
    return result
def sdd_disjunctive_of_terms(manager, variables, positive_variable_tuples):
    result = sdd.sdd_manager_false(manager)
    for positive_tuple in positive_variable_tuples:
        cur_term = sdd_term(manager, variables, positive_tuple)
        result = sdd.sdd_disjoin(result, cur_term, manager)
    return result

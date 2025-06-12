def parse_expression(expression, variables):
    """
    parse expression, support variable substitution
    
    Args:
        expression (str): the expression to parse
        variables (dict): 变量字典
    
    Returns:
        str: parsed expression
    """
    if not expression:
        return expression
    
    # simple variable substitution implementation
    for key, value in variables.items():
        placeholder = f"${{{key}}}"
        if placeholder in expression:
            expression = expression.replace(placeholder, str(value))
    
    return expression 
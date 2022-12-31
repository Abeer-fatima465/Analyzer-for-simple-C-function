//
// Analyzer for simple C programs.  This component performs
// semantic analysis, in particular collecting variable
// names and their types. The analysis also checks to ensure
// variable names are unique --- no duplicates.
//
// If all is well, a "symbol table" is built and returned,
// containing all variables and their types. A symbol table
// is a list of tuples of the form (name, type).  Example:
//
//   [("x", "int"); ("y", "int"); ("z", "real")]
//
// Modified by:
//   << YOUR NAME >>
//
// Original author:
//   Prof. Joe Hummel
//   U. of Illinois, Chicago
//   CS 341, Spring 2022
//

namespace compiler

module analyzer =

  let private matchToken expected_token (tokens: string list) =
    //
    // if the next token matches the expected token,  
    // keep parsing by returning the rest of the tokens.
    // Otherwise throw an exception because there's a 
    // syntax error, effectively stopping compilation:
    //
    // NOTE: identifier, int_literal and str_literal
    // are special cases because they are followed by
    // the name or literal value. In these cases exact
    // matching will not work, so we match the start 
    // of the token in these cases.
    //
    let next_token = List.head tokens

    if expected_token = "identifier" && next_token.StartsWith("identifier") then
      //
      // next_token starts with identifier, so we have a match:
      //
      (List.tail tokens, (List.head tokens).[11..])
    elif expected_token = "int_literal" && next_token.StartsWith("int_literal") then
      //
      // next_token starts with int_literal, so we have a match:
      //
      (List.tail tokens, "")
    elif expected_token = "str_literal" && next_token.StartsWith("str_literal") then
      //
      // next_token starts with str_literal, so we have a match:
      //
      (List.tail tokens, "")
    elif expected_token = "real_literal" && next_token.StartsWith("real_literal") then
      (List.tail tokens, "")
    elif expected_token = "real" && next_token = "int" then
      (List.tail tokens, "")
    elif expected_token = next_token then  
      (List.tail tokens, "")
    else
      failwith ("expecting " + expected_token + ", but found " + next_token)

  let rec private expr_value tokens =
    let next_token = List.head tokens
    //
    if next_token = "false" then
      let (T2, d) = matchToken "false" tokens
      T2
    elif next_token = "true" then
      let (T2, d) = matchToken "true" tokens
      T2
    //
    // the others are trickier since we have to look 
    // at the start of the string for a match:
    //
    elif next_token.StartsWith("identifier") then
      let (T2, d) = matchToken "identifier" tokens
      T2
    elif next_token.StartsWith("int_literal") then
      let (T2, d) = matchToken "int_literal" tokens
      T2
    elif next_token.StartsWith("real_literal") then
      let (T2, d) = matchToken "real_literal" tokens
      T2
    elif next_token.StartsWith("str_literal") then
      let (T2, d) = matchToken "str_literal" tokens
      T2
    else
      failwith ("expecting identifier or literal, but found " + next_token)

  let rec private expr_op tokens = 
    let next_token = List.head tokens
    //
    if next_token = "+"  ||
       next_token = "-"  ||
       next_token = "*"  ||
       next_token = "/"  ||
       next_token = "^"  ||
       next_token = "<"  ||
       next_token = "<=" ||
       next_token = ">"  ||
       next_token = ">=" ||
       next_token = "==" ||
       next_token = "!=" then
      //
      let (T2, d) = matchToken next_token tokens
      T2
    else
      // error
      failwith ("expecting expression operator, but found " + next_token)

  let rec private expr tokens = 
    //
    // first we have to match expr-value, since both
    // rules start with this:
    //
    let T2 = expr_value tokens
    //
    // now let's see if there's more to the expression:
    //
    let next_token = List.head T2
    //
    if next_token = "+"  ||
       next_token = "-"  ||
       next_token = "*"  ||
       next_token = "/"  ||
       next_token = "^"  ||
       next_token = "<"  ||
       next_token = "<=" ||
       next_token = ">"  ||
       next_token = ">=" ||
       next_token = "==" ||
       next_token = "!=" then
      //
      let T3 = expr_op T2
      let T4 = expr_value T3
      T4
    else
      // just expr_value, that's it
      T2

  //
  // NOTE: all functions in the module must be indented.
  //
  let rec private empty tokens = 
    let (T2, d) = matchToken ";" tokens
    T2

  //
  // <vardecl> -> int identifier ;
  //
  let rec private vardecl tokens = 
    let (T3, d) = matchToken "real" tokens
    let (T4, name) = matchToken "identifier" T3
    let (T5, d) = matchToken ";" T4
    (T5, name)

  let rec private input tokens = 
    let (T2, d) = matchToken "cin" tokens
    let (T3, d) = matchToken ">>" T2
    let (T4, d) = matchToken "identifier" T3
    let (T5, d) = matchToken ";" T4
    T5

  //
  // <output-value> -> <expr-value>
  //                 | endl
  //
  let rec private output_value tokens = 
    let next_token = List.head tokens
    //
    if next_token = "endl" then
      let (T2, d) = matchToken "endl" tokens
      T2
    else
      let T2 = expr_value tokens
      T2


  let rec private output tokens = 
    let (T2, d) = matchToken "cout" tokens
    let (T3, d) = matchToken "<<" T2
    let T4 = output_value T3
    let (T5, d) = matchToken ";" T4
    T5


  //
  // <assignment> -> identifier = <expr> ;
  //
  let rec private assignment tokens = 
    let (T2, d) = matchToken "identifier" tokens
    let (T3, d) = matchToken "=" T2
    let T4 = expr T3
    let (T5, d) = matchToken ";" T4
    T5

  let rec private stmt tokens table = 
    let next_token = List.head tokens
    //
    // use the next token to determine which rule
    // to call; if none match then it's a syntax
    // error:
    //
    if next_token = ";" then
      let T2 = empty tokens
      (T2, table)
    elif next_token = "int" then
      let (T2, name) = vardecl tokens
      let b = List.contains (name, "int") table
      let c = List.contains (name, "real") table
      if b || c then
        failwith ("redefinition of variable '" + name + "'")
      else
        (T2, (name, "int")::table)
    elif next_token = "real" then
      let (T2, name) = vardecl tokens
      let b = List.contains (name, "int") table
      let c = List.contains (name, "real") table
      if b || c then
        failwith ("redefinition of variable '" + name + "'")
      else
        (T2, (name, "real")::table)
    elif next_token = "cin" then
      let T2 = input tokens
      (T2, table)
    elif next_token = "cout" then
      let T2 = output tokens
      (T2, table)
    elif next_token.StartsWith("identifier") then
      let T2 = assignment tokens
      (T2, table)
    elif next_token = "if" then
      let T2 = ifstmt tokens
      (T2, table)
    else
      failwith ("expecting statement, but found " + next_token)

  and private ifstmt tokens = 
    let (T2, d) = matchToken "if" tokens
    let (T3, d) = matchToken "(" T2
    let T4 = condition T3
    let (T5, d) = matchToken ")" T4
    let T6 = then_part T5
    let T7 = else_part T6
    T7

  and private condition tokens = 
    let T2 = expr tokens
    T2
  //
  // <then-part> -> <stmt>
  //
  and private then_part tokens = 
    let (T2, table) = stmt tokens []
    T2

  and private else_part tokens = 
    let next_token = List.head tokens
    //
    if next_token = "else" then
      let (T2, d) = matchToken "else" tokens
      let (T3, table) = stmt T2 []
      T3
    else
      // EMPTY, do nothing but return tokens back
      tokens

  let rec private morestmts tokens table = 
    //
    // if the next token denotes the start of a stmt 
    // then process stmt and morestmts, otherwise apply
    // EMPTY
    //
    let next_token = List.head tokens
    //
    if next_token = ";"    ||
       next_token = "int"  ||
       next_token = "real" ||
       next_token = "cin"  ||
       next_token = "cout" ||
       next_token.StartsWith("identifier") ||
       next_token = "if" then
      //
      let (T2, table2) = stmt tokens table
      let (T3, table3) = morestmts T2 table2
      (T3, table3)
    else 
      // EMPTY => do nothing, just return tokens back
      (tokens, table)

  let rec private stmts tokens = 
    let (T2, table) = stmt tokens []
    let (T3, table2) = morestmts T2 table
    (T3, table2)

  let private simpleC tokens = 
    let (T2, d) = matchToken "void" tokens
    let (T3, d) = matchToken "main" T2
    let (T4, d) = matchToken "(" T3
    let (T5, d) = matchToken ")" T4
    let (T6, d) = matchToken "{" T5
    let (T7, table) = stmts T6
    let (T8, d) = matchToken "}" T7
    let (T9, d) = matchToken "$" T8  // $ => EOF, there should be no more tokens
    (T9, table)

  //
  // build_symboltable tokens
  //
  // Given a list of tokens, analyzes the program by looking
  // at variable declarations and collecting them into a
  // list. This list is known as a symbol table. Returns
  // a tuple (result, symboltable), where result is a string 
  // denoting "success" if valid, otherwise a string of the 
  // form "semantic_error:...".
  //
  // On success, the symboltable is a list of tuples of the
  // form (name, type), e.g. [("x","int"); ("y","real")]. On 
  // an error, the returned list is empty [].
  //
  let build_symboltable tokens = 
    try
      let (T2, symboltable) = simpleC tokens
      ("success", symboltable)
    with 
      | ex -> ("semantic_error: " + ex.Message, [])

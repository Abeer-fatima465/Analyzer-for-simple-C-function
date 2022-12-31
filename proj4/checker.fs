//
// Analyzer for simple C programs.  This component performs
// type checking.  The analyzer returns a string denoting
// success or failure. The string "success" if the input 
// program is legal, otherwise the string "type_error: ..." 
// is returned denoting an invalid simple C program.
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

module checker =
  //
  // NOTE: all functions in the module must be indented.
  //


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
      List.tail tokens
    elif expected_token = "int_literal" && next_token.StartsWith("int_literal") then
      //
      // next_token starts with int_literal, so we have a match:
      //
      List.tail tokens
    elif expected_token = "str_literal" && next_token.StartsWith("str_literal") then
      //
      // next_token starts with str_literal, so we have a match:
      //
      List.tail tokens
    elif expected_token = "real_literal" && next_token.StartsWith("real_literal") then
      List.tail tokens
    elif expected_token = "real" && next_token = "int" then
      List.tail tokens
    elif expected_token = next_token then  
      List.tail tokens
    else
      failwith ("expecting " + expected_token + ", but found " + next_token)

  let private declared table s =
    List.contains (s, "int") table || List.contains (s, "real") table


  //
  // <expr-value> -> identifier
  //               | int_literal
  //               | str_literal
  //               | true
  //               | false
  //
  let rec private expr_value tokens table =
    let next_token = List.head tokens
    //
    if next_token = "false" then
      let T2 = matchToken "false" tokens
      T2
    elif next_token = "true" then
      let T2 = matchToken "true" tokens
      T2
    //
    // the others are trickier since we have to look 
    // at the start of the string for a match:
    //
    elif next_token.StartsWith("identifier") then
      let T2 = matchToken "identifier" tokens

      let name = (List.head tokens).[11..]
      if not (declared table name) then
        failwith ("variable '" + name + "' undefined")

      T2
    elif next_token.StartsWith("int_literal") then
      let T2 = matchToken "int_literal" tokens
      T2
    elif next_token.StartsWith("real_literal") then
      let T2 = matchToken "real_literal" tokens
      T2
    elif next_token.StartsWith("str_literal") then
      let T2 = matchToken "str_literal" tokens
      T2
    else
      failwith ("expecting identifier or literal, but found " + next_token)


  //
  // <expr-op> -> +
  //            | -
  //            | *
  //            | /
  //            | ^
  //            | <
  //            | <=
  //            | >
  //            | >=
  //            | ==
  //            | !=
  //
  let rec private expr_op tokens table = 
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
      let T2 = matchToken next_token tokens
      T2
    else
      // error
      failwith ("expecting expression operator, but found " + next_token)


  let private get_type token table =
    if (string token).StartsWith("identifier") then
      let L = List.filter (fun (a, b) -> (a = (string token).[11..])) table
      let (a, b) = List.head L
      b
    elif token = "true" || token = "false" then
      "bool"
    else
      if (string token).StartsWith("real") then
        "real"
      elif (string token).StartsWith("int") then
        "int"
      elif (string token).StartsWith("str") then
        "str"
      else
        token

  //
  // <expr> -> <expr-value> <expr-op> <expr-value>
  //         | <expr-value>
  //
  let rec private expr tokens table = 
    //
    // first we have to match expr-value, since both
    // rules start with this:
    //
    let T2 = expr_value tokens table
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
      let T3 = expr_op T2 table
      let T4 = expr_value T3 table

      let type1 = get_type (List.head tokens) table
      let type2 = get_type (List.head T3) table

      if (type1 = "real" && next_token = "==" && type2 = "real") then
        printfn "warning: comparing real numbers with == may never be true"

      if next_token = "+" ||
         next_token = "-" ||
         next_token = "*" ||
         next_token = "/" ||
         next_token = "^" then
        if not (type1.StartsWith("int") || type1.StartsWith("real")) || not (type2.StartsWith("int") || type2.StartsWith("real")) then
          failwith ("operator " + next_token + " must involve 'int' or 'real'")
      else
        if not (type1 = type2) then
          failwith ("type mismatch '" + type1 + "' " + next_token + " '" + type2 + "'")
      T4
    else
      // just expr_value, that's it
      T2

  let rec private expr_cond tokens table =
    let T2 = expr_value tokens table
    //
    // now let's see if there's more to the expression:
    //
    let next_token = List.head T2
    //
    if next_token = "<"  ||
       next_token = "<=" ||
       next_token = ">"  ||
       next_token = ">=" ||
       next_token = "==" ||
       next_token = "!=" then
      //
      let T3 = expr_op T2 table
      let T4 = expr_value T3 table

      let type1 = get_type (List.head tokens) table
      let type2 = get_type (List.head T3) table

      if (type1 = "real" && next_token = "==" && type2 = "real") then
        printfn "warning: comparing real numbers with == may never be true"

      if next_token = "+" ||
         next_token = "-" ||
         next_token = "*" ||
         next_token = "/" ||
         next_token = "^" then
        if not (type1.StartsWith("int") || type1.StartsWith("real")) || not (type2.StartsWith("int") || type2.StartsWith("real")) then
          failwith ("operator " + next_token + " must involve 'int' or 'real'")
      else
        if not (type1 = type2) then
          failwith ("type mismatch '" + type1 + "' " + next_token + " '" + type2 + "'")

      T4
    else
      // just expr_value, that's it
      if not ((List.head tokens) = "false") && not ((List.head tokens) = "true") then
        failwith ("if condition must be 'bool', but found '" + (get_type (List.head tokens) table) + "'")
      T2

  
  //
  // <empty> -> ;
  //
  let rec private empty tokens = 
    let T2 = matchToken ";" tokens
    T2


  //
  // <vardecl> -> int identifier ;
  //
  let rec private vardecl tokens table = 
    let T3 = matchToken "real" tokens
    let T4 = matchToken "identifier" T3

    let name = (List.head T3).[11..]
    if not (declared table name) then
      failwith ("variable '" + name + "' undefined")

    let T5 = matchToken ";" T4
    T5


  //
  // <input> -> cin >> identifier ;
  //
  let rec private input tokens table = 
    let T2 = matchToken "cin" tokens
    let T3 = matchToken ">>" T2
    let T4 = matchToken "identifier" T3
    
    let name = (List.head T3).[11..]
    if not (declared table name) then
      failwith ("variable '" + name + "' undefined")

    let T5 = matchToken ";" T4
    T5


  //
  // <output-value> -> <expr-value>
  //                 | endl
  //
  let rec private output_value tokens table = 
    let next_token = List.head tokens
    //
    if next_token = "endl" then
      let T2 = matchToken "endl" tokens
      T2
    else
      let T2 = expr_value tokens table
      T2


  //
  // <output> -> cout << <output-value> ;
  //
  let rec private output tokens table = 
    let T2 = matchToken "cout" tokens
    let T3 = matchToken "<<" T2
    let T4 = output_value T3 table
    let T5 = matchToken ";" T4
    T5

  let private expr_type tokens table =
    let op = List.head (List.tail tokens)
    if op = "==" ||
       op = "!=" ||
       op = "<"  ||
       op = ">"  ||
       op = "<=" ||
       op = ">=" then
      "bool"
    else
      let type1 = get_type (List.head tokens) table
      let type2 = get_type (List.head (List.tail (List.tail tokens))) table
      if type1 = "real" || type2 = "real" then
        "real"
      else
        "int"

  //
  // <assignment> -> identifier = <expr> ;
  //
  let rec private assignment tokens table = 
    let T2 = matchToken "identifier" tokens

    let name = (List.head tokens).[11..]
    if not (declared table name) then
      failwith ("variable '" + name + "' undefined")

    let T3 = matchToken "=" T2
    let T4 = expr T3 table

    let exprtype = expr_type T3 table

    let type1 = get_type (List.head tokens) table
    let type2 = get_type (List.head T3) table

    if exprtype = "bool" then
      failwith ("cannot assign 'bool' to variable of type '" + type1 + "'")

    if not (type1 = type2) && not (type1 = "real" && type2 = "int") then
      failwith ("cannot assign '" + type2 + "' to variable of type '" + type1 + "'")

    let T5 = matchToken ";" T4
    T5


  //
  // <stmt> -> <empty>
  //         | <vardecl>
  //         | <input>
  //         | <output>
  //         | <assignment>
  //         | <ifstmt>
  //
  let rec private stmt tokens table = 
    let next_token = List.head tokens
    //
    // use the next token to determine which rule
    // to call; if none match then it's a syntax
    // error:
    //
    if next_token = ";" then
      let T2 = empty tokens
      T2
    elif next_token = "int" || next_token = "real" then
      let T2 = vardecl tokens table
      T2
    elif next_token = "cin" then
      let T2 = input tokens table
      T2
    elif next_token = "cout" then
      let T2 = output tokens table
      T2
    elif next_token.StartsWith("identifier") then
      let T2 = assignment tokens table
      T2
    elif next_token = "if" then
      let T2 = ifstmt tokens table
      T2
    else
      failwith ("expecting statement, but found " + next_token)
  //
  // <ifstmt> -> if ( <condition> ) <then-part> <else-part>
  //
  and private ifstmt tokens table = 
    let T2 = matchToken "if" tokens
    let T3 = matchToken "(" T2
    let T4 = condition T3 table
    let T5 = matchToken ")" T4
    let T6 = then_part T5 table
    let T7 = else_part T6 table
    T7
  //
  // <condition> -> <expr>
  //
  and private condition tokens table = 
    let T2 = expr_cond tokens table 
    T2
  //
  // <then-part> -> <stmt>
  //
  and private then_part tokens table = 
    let T2 = stmt tokens table
    T2
  //
  // <else-part> -> else <stmt>
  //              | EMPTY
  //
  and private else_part tokens table = 
    let next_token = List.head tokens
    //
    if next_token = "else" then
      let T2 = matchToken "else" tokens
      let T3 = stmt T2 table
      T3
    else
      // EMPTY, do nothing but return tokens back
      tokens


  //
  // <morestmts> -> <stmt> <morestmts>
  //              | EMPTY
  //
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
      let T2 = stmt tokens table
      let T3 = morestmts T2 table
      T3
    else 
      // EMPTY => do nothing, just return tokens back
      tokens


  //
  // <stmts> -> <stmt> <morestmts>
  // 
  let rec private stmts tokens table = 
    let T2 = stmt tokens table
    let T3 = morestmts T2 table
    T3


  //
  // <simpleC> -> void main ( ) { <stmts> } $
  //
  let private simpleC tokens table = 
    let T2 = matchToken "void" tokens
    let T3 = matchToken "main" T2
    let T4 = matchToken "("    T3
    let T5 = matchToken ")"    T4
    let T6 = matchToken "{"    T5
    let T7 = stmts             T6 table
    let T8 = matchToken "}"    T7
    let T9 = matchToken "$"    T8  // $ => EOF, there should be no more tokens
    T9


  //
  // typecheck tokens symboltable
  //
  // Given a list of tokens and a symbol table, type-checks 
  // the program to ensure program's variables and expressions
  // are type-compatible. If the program is valid, returns 
  // the string "success". If the program contains a semantic
  // error or warning, returns a string of the form
  // "type_error: ...".
  //
  let typecheck tokens symboltable = 
    try
      let T2 = simpleC tokens symboltable
      "success"
    with 
      | ex -> "type_error: " + ex.Message


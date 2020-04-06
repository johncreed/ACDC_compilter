#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <string.h>
#include <assert.h>
#include "header.h"

int main( int argc, char *argv[] )
{
    FILE *source, *fout;
    Program program;
    SymbolTable symtab;

    if(argc == 3){
        fout = fopen(argv[2], "w");
        if( !fout ){
            printf("can't open the fout file\n");
            exit(2);
        }
    }
    else{
        fout = stdout;
    }

    if( argc == 2 || argc == 3 ){
        source = fopen(argv[1], "r");
        if( !source ){
            printf("can't open the source file\n");
            exit(2);
        }

        // Built AST
        fprintf(stderr, ">>>>>>>>>>>>>>>>>>>>>>> begin parse <<<<<<<<<<<<<<<<<<<<<<<<<<<<\n");
        program = parser(source);
        fclose(source);
        
        // Build table
        fprintf(stderr, ">>>>>>>>>>>>>>>>>>>>>>> begin table <<<<<<<<<<<<<<<<<<<<<<<<<<<<\n");
        symtab = build(program);

        // Check and convertIntToFloat...
        fprintf(stderr, ">>>>>>>>>>>>>>>>>>>>>>> begin check <<<<<<<<<<<<<<<<<<<<<<<<<<<<\n");
        check(&program, &symtab);

        // Print Dc code
        fprintf(stderr, ">>>>>>>>>>>>>>>>>>>>>>> begin print dc <<<<<<<<<<<<<<<<<<<<<<<<<<<<\n");
        gencode(program, fout);
    }
    else{
        printf("Usage: %s source_file [fout_file]\n", argv[0]);
    }

    fflush(stdout);

    return 0;
}


/********************************************* 
  Scanning 
 *********************************************/

void unget_tok(Token token,  FILE *source){

    fprintf(stderr, "unget_tok: %s\n", token.tok);
    int l = strlen(token.tok);
    for(int i = 0; i < l; i++){
        ungetc(token.tok[l-1-i], source);
    }
}

Token getNumericToken( FILE *source, char c )
{
    Token token;
    int i = 0;

    while( isdigit(c) ) {
        token.tok[i++] = c;
        c = fgetc(source);
    }

    if( c != '.' ){
        ungetc(c, source);
        token.tok[i] = '\0';
        token.type = IntValue;
        return token;
    }

    token.tok[i++] = '.';

    c = fgetc(source);
    if( !isdigit(c) ){
        ungetc(c, source);
        printf("Expect a digit : %c\n", c);
        exit(1);
    }

    while( isdigit(c) ){
        token.tok[i++] = c;
        c = fgetc(source);
    }

    ungetc(c, source);
    token.tok[i] = '\0';
    token.type = FloatValue;

    return token;
}

Token getLowerToken( FILE *source, char c )
{
    Token token;
    int i = 0;

    while( islower(c) ) {
        token.tok[i++] = c;
        c = fgetc(source);
    }
    ungetc(c, source);

    token.tok[i] = '\0';

    if( i == 1 ){
        char c = token.tok[0];
        if( c == 'f' )
            token.type = FloatDeclaration;
        else if( c == 'i' )
            token.type = IntegerDeclaration;
        else if( c == 'p' )
            token.type = PrintOp;
        else
            token.type = Alphabet;
    }
    else{
        token.type = Alphabet;
    }

    return token;
}

Token scanner( FILE *source )
{
    char c;
    Token token;

    while( !feof(source) ){
        c = fgetc(source);

        while( isspace(c) ) c = fgetc(source);

        if( isdigit(c) )
            return getNumericToken(source, c);

        if( islower(c) )
            return getLowerToken(source, c);

        token.tok[0] = c;
        token.tok[1] = '\0';
        switch(c){
            case '=':
                token.type = AssignmentOp;
                return token;
            case '+':
                token.type = PlusOp;
                return token;
            case '-':
                token.type = MinusOp;
                return token;
            case '*':
                token.type = MulOp;
                return token;
            case '/':
                token.type = DivOp;
                return token;
            case EOF:
                token.type = EOFsymbol;
                token.tok[0] = '\0';
                return token;
            default:
                printf("Invalid character : %c\n", c);
                exit(1);
        }
    }

    token.tok[0] = '\0';
    token.type = EOFsymbol;
    return token;
}


/********************************************************
  Parsing
 *********************************************************/
Declaration parseDeclaration( FILE *source, Token token )
{
    Token token2;
    switch(token.type){
        case FloatDeclaration:
        case IntegerDeclaration:
            token2 = scanner(source);
            if (strcmp(token2.tok, "f") == 0 ||
                    strcmp(token2.tok, "i") == 0 ||
                    strcmp(token2.tok, "p") == 0) {
                printf("Syntax Error: \"%s\" cannot be used as id\n", token2.tok);
                exit(1);
            }
            return makeDeclarationNode( token, token2 );
        default:
            printf("Syntax Error: Expect Declaration %s\n", token.tok);
            exit(1);
    }
}

Declarations *parseDeclarations( FILE *source )
{
    Token token = scanner(source);
    Declaration decl;
    Declarations *decls;
    switch(token.type){
        case FloatDeclaration:
        case IntegerDeclaration:
            decl = parseDeclaration(source, token);
            decls = parseDeclarations(source);
            return makeDeclarationTree( decl, decls );
        case PrintOp:
        case Alphabet:
            unget_tok(token, source);
            return NULL;
        case EOFsymbol:
            return NULL;
        default:
            printf("Syntax Error: Expect declarations %s\n", token.tok);
            exit(1);
    }
}

Expression *parseValue( FILE *source )
{
    Token token = scanner(source);
    Expression *value = (Expression *)malloc( sizeof(Expression) );
    value->leftOperand = value->rightOperand = NULL;

    switch(token.type){
        case Alphabet:
            (value->v).type = Identifier;
            strcpy( (value->v).val.id, token.tok );
            break;
        case IntValue:
            (value->v).type = IntConst;
            (value->v).val.ivalue = atoi(token.tok);
            break;
        case FloatValue:
            (value->v).type = FloatConst;
            (value->v).val.fvalue = atof(token.tok);
            break;
        default:
            printf("Syntax Error: Expect Identifier or a Number %s\n", token.tok);
            exit(1);
    }

    return value;
}

Expression *parseMulDivExpressionTail( FILE *source, Expression *lvalue )
{
    Token token = scanner(source);
    Expression *expr;

    switch(token.type){
        case MulOp:
            expr = (Expression *)malloc( sizeof(Expression) );
            (expr->v).type = MulNode;
            (expr->v).val.op = Mul;
            expr->leftOperand = lvalue;
            expr->rightOperand = parseValue(source);
            return parseMulDivExpressionTail(source, expr);
        case DivOp:
            expr = (Expression *)malloc( sizeof(Expression) );
            (expr->v).type = DivNode;
            (expr->v).val.op = Div;
            expr->leftOperand = lvalue;
            expr->rightOperand = parseValue(source);
            return parseMulDivExpressionTail(source, expr);
        case Alphabet:
            unget_tok(token, source );
            return lvalue;
        case PlusOp:
        case MinusOp:
        case PrintOp:
            ungetc(token.tok[0], source);
            return lvalue;
        case EOFsymbol:
            return lvalue;
        default:
            printf("Syntax Error: Expect a numeric value or an identifier %s\n", token.tok);
            exit(1);
    }
}

Expression *parseExpressionTail( FILE *source, Expression *lvalue )
{
    Token token = scanner(source);
    Expression *expr;

    switch(token.type){
        case PlusOp:
            expr = (Expression *)malloc( sizeof(Expression) );
            (expr->v).type = PlusNode;
            (expr->v).val.op = Plus;
            expr->leftOperand = lvalue;
            expr->rightOperand = parseMulDivExpressionTail( source, parseValue(source) );
            return parseExpressionTail(source, expr);
        case MinusOp:
            expr = (Expression *)malloc( sizeof(Expression) );
            (expr->v).type = MinusNode;
            (expr->v).val.op = Minus;
            expr->leftOperand = lvalue;
            expr->rightOperand = parseMulDivExpressionTail( source, parseValue(source) );
            return parseExpressionTail(source, expr);
        case Alphabet:
            unget_tok(token, source );
            return lvalue;
        case PrintOp:
            ungetc(token.tok[0], source);
            return lvalue;
        case EOFsymbol:
            return lvalue;
        default:
            printf("Syntax Error: Expect a numeric value or an identifier %s\n", token.tok);
            exit(1);
    }
}

Expression *parseExpression( FILE *source, Expression *lvalue )
{
    Token token = scanner(source);
    Expression *expr;

    switch(token.type){
        case PlusOp:
            expr = (Expression *)malloc( sizeof(Expression) );
            (expr->v).type = PlusNode;
            (expr->v).val.op = Plus;
            expr->leftOperand = lvalue;
            expr->rightOperand = parseMulDivExpressionTail( source, parseValue(source) );
            return parseExpressionTail(source, expr);
        case MinusOp:
            expr = (Expression *)malloc( sizeof(Expression) );
            (expr->v).type = MinusNode;
            (expr->v).val.op = Minus;
            expr->leftOperand = lvalue;
            expr->rightOperand = parseMulDivExpressionTail( source, parseValue(source) );
            return parseExpressionTail(source, expr);
        case MulOp:
            expr = (Expression *)malloc( sizeof(Expression) );
            (expr->v).type = MulNode;
            (expr->v).val.op = Mul;
            expr->leftOperand = lvalue;
            expr->rightOperand = parseValue(source);
            return parseExpressionTail( source, parseMulDivExpressionTail(source, expr) );
        case DivOp:
            expr = (Expression *)malloc( sizeof(Expression) );
            (expr->v).type = DivNode;
            (expr->v).val.op = Div;
            expr->leftOperand = lvalue;
            expr->rightOperand = parseValue(source);
            return parseExpressionTail( source, parseMulDivExpressionTail(source, expr) );
        case Alphabet:
            unget_tok(token, source );
            return lvalue;
        case PrintOp:
            ungetc(token.tok[0], source);
            return NULL;
        case EOFsymbol:
            return NULL;
        default:
            printf("Syntax Error: Expect a numeric value or an identifier %s\n", token.tok);
            exit(1);
    }
}

Statement parseStatement( FILE *source, Token token )
{
    Token next_token;
    Expression *value, *expr;

    switch(token.type){
        case Alphabet:
            next_token = scanner(source);
            if(next_token.type == AssignmentOp){
                value = parseValue(source); // get id, int, float
                expr = parseExpression(source, value); 
                return makeAssignmentNode(token.tok, value, expr);
            }
            else{
                printf("Syntax Error: Expect an assignment op %s\n", next_token.tok);
                exit(1);
            }
        case PrintOp:
            next_token = scanner(source);
            if(next_token.type == Alphabet)
                return makePrintNode(next_token.tok);
            else{
                printf("Syntax Error: Expect an identifier %s\n", next_token.tok);
                exit(1);
            }
            break;
        default:
            printf("Syntax Error: Expect a statement %s\n", token.tok);
            exit(1);
    }
}

Statements *parseStatements( FILE * source )
{

    Token token = scanner(source);
    Statement stmt;
    Statements *stmts;

    switch(token.type){
        case Alphabet:
        case PrintOp:
            stmt = parseStatement(source, token);
            stmts = parseStatements(source);
            return makeStatementTree(stmt , stmts); // stmt1->stmt2 (linked-list)
        case EOFsymbol:
            return NULL;
        default:
            printf("Syntax Error: Expect statements %s\n", token.tok);
            exit(1);
    }
}


/*********************************************************************
  Build AST
 **********************************************************************/
Declaration makeDeclarationNode( Token declare_type, Token identifier )
{
    Declaration tree_node;

    switch(declare_type.type){
        case FloatDeclaration:
            tree_node.type = Float;
            break;
        case IntegerDeclaration:
            tree_node.type = Int;
            break;
        default:
            break;
    }

    strcpy( tree_node.name, identifier.tok );

    return tree_node;
}

Declarations *makeDeclarationTree( Declaration decl, Declarations *decls )
{
    Declarations *new_tree = (Declarations *)malloc( sizeof(Declarations) );
    new_tree->first = decl;
    new_tree->rest = decls;

    return new_tree;
}


Statement makeAssignmentNode( char *id, Expression *v, Expression *expr_tail )
{
    Statement stmt;
    AssignmentStatement assign;

    stmt.type = Assignment;
    strcpy( assign.id, id );
    if(expr_tail == NULL)
        assign.expr = v;
    else
        assign.expr = expr_tail;
    stmt.stmt.assign = assign;

    return stmt;
}

Statement makePrintNode( char *id )
{
    Statement stmt;
    stmt.type = Print;
    strcpy( stmt.stmt.variable, id);

    return stmt;
}

Statements *makeStatementTree( Statement stmt, Statements *stmts )
{
    Statements *new_tree = (Statements *)malloc( sizeof(Statements) );
    new_tree->first = stmt;
    new_tree->rest = stmts;

    return new_tree;
}

/* parser */
Program parser( FILE *source )
{
    Program program;

    program.declarations = parseDeclarations(source);
    program.statements = parseStatements(source);

    return program;
}


/********************************************************
  Build symbol table
 *********************************************************/
void InitializeTable( SymbolTable *table )
{
    int i;
    table->size = 0;
    for(i = 0 ; i < 26; i++)
        table->table[i] = Notype;
}

int is_defined( SymbolTable *table, char *c){
    //fprintf(stderr, "---------------\n");
    int size = table->size;
    
    for(int i = 0; i < size; i++){
        //fprintf(stderr, "check define %d (%s,%s)\n", i, table->id[i], c);
        if( strcmp( table->id[i], c ) == 0 )
            return i;
    }
    return -1;
}

void add_table( SymbolTable *table, char *c, DataType t )
{
    if( table->size >= 1  && is_defined( table, c ) != -1 ){
        fprintf(stderr, "Syntax Error : id %s has been declared\n", c);//error
        exit(1);
    }

    table->table[table->size] = t;
    strcpy( table->id[table->size], c);
    table->size++;
}

SymbolTable build( Program program )
{
    SymbolTable table;
    Declarations *decls = program.declarations;
    Declaration current;

    InitializeTable(&table);

    while(decls !=NULL){
        current = decls->first;
        add_table(&table, current.name, current.type);
        decls = decls->rest;
    }

    printf("==== Variable Table =====\n");
    for(int i = 0; i < table.size; i++){
       printf("%s,\t", table.id[i]);
    }
    printf("\n=========================\n");

    return table;
}


/********************************************************************
  Type checking
 *********************************************************************/

void convertType( Expression * old, DataType type )
{
    if(old->type == Float && type == Int){
        printf("error : can't convert float to integer\n");
        exit(1);
        return;
    }
    if(old->type == Int && type == Float){
        Expression *tmp = (Expression *)malloc( sizeof(Expression) );
        if(old->v.type == Identifier)
            printf("convert to float %s \n",old->v.val.id);
        else
            printf("convert to float %d \n", old->v.val.ivalue);
        tmp->v = old->v;
        tmp->leftOperand = old->leftOperand;
        tmp->rightOperand = old->rightOperand;
        tmp->type = old->type;

        Value v;
        v.type = IntToFloatConvertNode;
        v.val.op = IntToFloatConvert;
        old->v = v;
        old->type = Int;
        old->leftOperand = tmp;
        old->rightOperand = NULL;
    }
}

DataType generalize( Expression *left, Expression *right )
{
    if(left->type == Float || right->type == Float){
        printf("generalize : float\n");
        return Float;
    }
    printf("generalize : int\n");
    return Int;
}

DataType lookup_table( SymbolTable *table, char *c )
{
    int idx = is_defined( table, c);
    if( idx == -1 ){
        printf("Syntax Error : identifier \"%s\" is not declared\n", c);//error
        exit(1);
    }
    return table->table[idx];
}

void checkexpression( Expression * expr, SymbolTable * table )
{
    char *c;
    if(expr->leftOperand == NULL && expr->rightOperand == NULL){
        switch(expr->v.type){
            case Identifier:
                c = expr->v.val.id;
                printf("identifier : %s\n",c);
                expr->type = lookup_table(table, c);
                break;
            case IntConst:
                printf("constant : int\n");
                expr->type = Int;
                break;
            case FloatConst:
                printf("constant : float\n");
                expr->type = Float;
                break;
                //case PlusNode: case MinusNode: case MulNode: case DivNode:
            default:
                break;
        }
    }
    else{
        Expression *left = expr->leftOperand;
        Expression *right = expr->rightOperand;

        checkexpression(left, table);
        checkexpression(right, table);

        DataType type = generalize(left, right);
        convertType(left, type);//left->type = type;//converto
        convertType(right, type);//right->type = type;//converto
        expr->type = type;
    }
}

Value merge_const_val( Operation op, Value &lhs, Value &rhs ){
    assert( lhs.type == rhs.type );
    Value v;
    v.type = lhs.type;

    if( v.type == IntConst ){
        int lval = lhs.val.ivalue, rval = rhs.val.ivalue;
        switch(op){
            case Minus:
                v.val.ivalue = lval - rval;
                printf("Fold %d - %d\n", lval, rval);
                break;
            case Plus:
                v.val.ivalue = lval + rval;
                printf("Fold %d + %d\n", lval, rval);
                break;
            case Mul:
                v.val.ivalue = lval * rval;
                printf("Fold %d * %d\n", lval, rval);
                break;
            case Div:
                v.val.ivalue = lval / rval;
                printf("Fold %d / %d\n", lval, rval);
                break;
            default:
                printf("Error in folding = %d\n",op);
                exit(1);
                break;
        }
    }
    else{
        float lval = lhs.val.fvalue, rval = rhs.val.fvalue;
        switch(op){
            case Minus:
                v.val.fvalue = lval - rval;
                printf("Fold %.6f - %.6f\n", lval, rval);
                break;
            case Plus:
                v.val.fvalue = lval + rval;
                printf("Fold %.6f + %.6f\n", lval, rval);
                break;
            case Mul:
                v.val.fvalue = lval * rval;
                printf("Fold %.6f * %.6f\n", lval, rval);
                break;
            case Div:
                v.val.fvalue = lval / rval;
                printf("Fold %.6f / %.6f\n", lval, rval);
                break;
            default:
                printf("Error in folding = %d\n",op);
                exit(1);
                break;
        }
    }

    return v;
}

Expression *fold( Expression *expr ){
    if(expr == NULL)
        return NULL;

    if(expr->leftOperand == NULL && expr->rightOperand == NULL)
        return expr;

    Expression *left = fold( expr->leftOperand );
    Expression *right = fold( expr->rightOperand );
   
    if( left != NULL && right == NULL ){
        ValueType l_type = left->v.type;

        if(expr->v.type == IntToFloatConvertNode && l_type == IntConst ){
            Value v;
            v.type = FloatConst;
            v.val.fvalue = left->v.val.ivalue;

            free(left);
            expr->v = v;
            expr->leftOperand = expr->rightOperand = NULL;
            printf("Implicit convert const Int to Float\n");
        }
    }
    else if( left != NULL && right != NULL){
        ValueType l_type = left->v.type, r_type = right->v.type;

        if( (l_type == IntConst || l_type == FloatConst) && (r_type == IntConst || r_type == FloatConst) ){
            assert( l_type == r_type );
            
            Value v = merge_const_val( expr->v.val.op, left->v, right->v );
            free( left );
            free( right );
            expr->leftOperand = expr->rightOperand = NULL;
            expr->v = v;
        }
    }


    return expr;
}

void checkstmt( Statement *stmt, SymbolTable * table )
{
    if(stmt->type == Assignment){
        AssignmentStatement assign = stmt->stmt.assign;
        printf("assignment : %s \n",assign.id);
        checkexpression(assign.expr, table);
        assign.expr = fold( assign.expr );
        stmt->stmt.assign.type = lookup_table(table, assign.id);
        if (assign.expr->type == Float && stmt->stmt.assign.type == Int) {
            printf("error : can't convert float to integer\n");
            exit(1);
        } else {
            convertType(assign.expr, stmt->stmt.assign.type);
        }
    }
    else if (stmt->type == Print){
        printf("print : %s \n",stmt->stmt.variable);
        lookup_table(table, stmt->stmt.variable);
    }
    else printf("error : statement error\n");//error
}

void check( Program *program, SymbolTable * table )
{
    Statements *stmts = program->statements;
    while(stmts != NULL){
        checkstmt(&stmts->first,table); // chech and convertIntToFloat ....
        stmts = stmts->rest;
    }
}


/***********************************************************************
  Code generation
 ************************************************************************/
void fprint_op( FILE *fout, ValueType op )
{
    switch(op){
        case MinusNode:
            fprintf(fout,"-\n");
            break;
        case PlusNode:
            fprintf(fout,"+\n");
            break;
        case MulNode:
            fprintf(fout,"*\n");
            break;
        case DivNode:
            fprintf(fout,"/\n");
            break;
        default:
            fprintf(fout,"Error in fprintf_op ValueType = %d\n",op);
            break;
    }
}

void fprint_expr( FILE *fout, Expression *expr)
{

    if(expr->leftOperand == NULL){
        switch( (expr->v).type ){
            case Identifier:
                fprintf(fout,"l%s\n",(expr->v).val.id);
                break;
            case IntConst:
                fprintf(fout,"%d\n",(expr->v).val.ivalue);
                break;
            case FloatConst:
                fprintf(fout,"%f\n", (expr->v).val.fvalue);
                break;
            default:
                fprintf(fout,"Error In fprint_left_expr. (expr->v).type=%d\n",(expr->v).type);
                break;
        }
    }
    else{
        fprint_expr(fout, expr->leftOperand);
        if(expr->rightOperand == NULL){
            fprintf(fout,"5 k\n");
        }
        else{
            fprint_expr(fout, expr->rightOperand);
            fprint_op(fout, (expr->v).type);
        }
    }
}

void gencode(Program prog, FILE * fout)
{
    Statements *stmts = prog.statements;
    Statement stmt;

    // Iterate all statements
    while(stmts != NULL){
        stmt = stmts->first;
        switch(stmt.type){
            case Print:
                fprintf(fout,"l%s\n",stmt.stmt.variable);
                fprintf(fout,"p\n");
                fprintf(fout,"si\n");
                break;
            case Assignment:
                fprint_expr(fout, stmt.stmt.assign.expr);
                /*
                   if(stmt.stmt.assign.type == Int){
                   fprintf(fout,"0 k\n");
                   }
                   else if(stmt.stmt.assign.type == Float){
                   fprintf(fout,"5 k\n");
                   }*/
                fprintf(fout,"s%s\n",stmt.stmt.assign.id);
                fprintf(fout,"0 k\n");
                break;
        }
        stmts=stmts->rest;
    }

}


/***************************************
  For our debug,
  you can omit them.
 ****************************************/
void print_expr(Expression *expr)
{
    if(expr == NULL)
        return;
    else{
        print_expr(expr->leftOperand);
        switch((expr->v).type){
            case Identifier:
                printf("%s ", (expr->v).val.id);
                break;
            case IntConst:
                printf("%d ", (expr->v).val.ivalue);
                break;
            case FloatConst:
                printf("%f ", (expr->v).val.fvalue);
                break;
            case PlusNode:
                printf("+ ");
                break;
            case MinusNode:
                printf("- ");
                break;
            case MulNode:
                printf("* ");
                break;
            case DivNode:
                printf("/ ");
                break;
            case IntToFloatConvertNode:
                printf("(float) ");
                break;
            default:
                printf("error ");
                break;
        }
        print_expr(expr->rightOperand);
    }
}

void test_parser( FILE *source )
{
    Declarations *decls;
    Statements *stmts;
    Declaration decl;
    Statement stmt;
    Program program = parser(source);

    decls = program.declarations;

    while(decls != NULL){
        decl = decls->first;
        if(decl.type == Int)
            printf("i ");
        if(decl.type == Float)
            printf("f ");
        printf("%s ",decl.name);
        decls = decls->rest;
    }

    stmts = program.statements;

    while(stmts != NULL){
        stmt = stmts->first;
        if(stmt.type == Print){
            printf("p %s ", stmt.stmt.variable);
        }

        if(stmt.type == Assignment){
            printf("%s = ", stmt.stmt.assign.id);
            print_expr(stmt.stmt.assign.expr);
        }
        stmts = stmts->rest;
    }

}

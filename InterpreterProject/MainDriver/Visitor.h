#pragma once
#include <iostream>
#include <string>
#include "Absyn.h"

using namespace std;
using namespace absyn;

namespace semantics
{
	class Visitor
	{
	public:
		virtual void visit(const Absyn *v) = 0;
		virtual void visit(const SimpleVar *v) = 0;
		virtual void visit(const FieldVar *v) = 0;
		virtual void visit(const SubscriptVar *v) = 0;
		virtual void visit(const Var *v) = 0;
		virtual void visit(const OpExp *e) = 0;
		virtual void visit(const VarExp *e) = 0;
		virtual void visit(const NilExp *e) = 0;
		virtual void visit(const IntExp *e) = 0;
		virtual void visit(const StringExp *e) = 0;
		virtual void visit(const CallExp *e) = 0;
		virtual void visit(const RecordExp *e) = 0;
		virtual void visit(const SeqExp *e) = 0;
		virtual void visit(const AssignExp *e) = 0;
		virtual void visit(const IfExp *e) = 0;
		virtual void visit(const WhileExp *e) = 0;
		virtual void visit(const ForExp *e) = 0;
		virtual void visit(const BreakExp *e) = 0;
		virtual void visit(const LetExp *e) = 0;
		virtual void visit(const ArrayExp *e) = 0;
		virtual void visit(const FunctionDec *d) = 0;
		virtual void visit(const VarDec *d) = 0;
		virtual void visit(const TypeDec *d) = 0;
		virtual void visit(const Dec *d) = 0;
		virtual void visit(const NameTy *t) = 0;
		virtual void visit(const RecordTy *t) = 0;
		virtual void visit(const ArrayTy *t) = 0;
		virtual void visit(const Ty *t) = 0;
	};
} // end of namespace semantics


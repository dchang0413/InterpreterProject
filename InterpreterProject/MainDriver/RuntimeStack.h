#pragma once

#include <deque>
#include "ActivationRecord.h"

namespace runtime
{
	class RuntimeStack
	{
	public:
		RuntimeStack(void) 
		{
			//push the AR that represents the global scope
			RTstack.push_back( ActivationRecord(NULL, NULL) ); 
		}

		~RuntimeStack(void) {};

		//get the topmost activation record whose level is <= the netstingLevel
		//if nestingLevel is -1, returns the top most AR
		ActivationRecord * getTopmost(int nestingLevel=-1);

		//push a new activation record to the top of the stack
		//the AR is a function call of funDef
		void push(symbol::SymTabEntry* funDef);

		//remove the topmost activation record
		void pop();

		//insert a new variable into the current scope of the topmost activation record
		void insert(string variable, VarEntry value);

		//update the value of a variable
		//the variable may be in the top AR, but it maybe in the AR that containing
		//the definition of current function
		void update(string variable, VarEntry value);

		//search for the value of the given variable
		VarEntry& lookup(string variable);

		//start a new scope level in current activation record
		void beginScope();
		//ends a new scope level in current activation record
		void endScope();

	private:
		std::deque<ActivationRecord>	RTstack;	//first item is the bottom of the stack
	};
}


#include "RuntimeStack.h"

namespace runtime
{
	//get the topmost activation record whose level is <= the netstingLevel
	//if nestingLevel is -1, returns the top most AR
	ActivationRecord * RuntimeStack::getTopmost(int nestingLevel)
	{
		if ( nestingLevel == -1 )
			return &RTstack[RTstack.size()-1];

		for(int i=RTstack.size()-1; i>=0; --i)
		{
			if (RTstack[i].getNestingLevel() <= nestingLevel)
				return &(RTstack[i]);
		}
		throw runtime_error("wrong nesting level argument");
	}

	//push a new activation record to the top of the stack
	//the AR is a function call of funDef
	void RuntimeStack::push(symbol::SymTabEntry* funDef)
	{
		int		level = funDef->level;
		ActivationRecord *parent = getTopmost(level - 1);

		ActivationRecord current(parent, funDef);
		
		RTstack.push_back( current );
	}

	//remove the topmost activation record
	void RuntimeStack::pop()
	{
		RTstack.pop_back();
	}

	//insert a new variable into the current scope of the topmost activation record
	void RuntimeStack::insert(string variable, VarEntry value)
	{
		RTstack[RTstack.size()-1].getMapping()->insert(variable, value);
	}

	//update the value of a variable
	//the variable may be in the top AR, but it maybe in the AR that containing
	//the definition of current function
	void RuntimeStack::update(string variable, VarEntry value)
	{
		ActivationRecord	*current = &RTstack[RTstack.size()-1];

		//Found in topmost AR
		if ( current->getMapping()->contains(variable) )
		{
			current->getMapping()->lookup(variable) = value;
			return;
		}

		//Not found in topmost AR, continue search on Parents, Grandparents ...
		while( current != NULL )
		{
			if ( current->getMapping()->globalContains(variable) )
			{
				current->getMapping()->globalLookup(variable) = value;
				return;
			}
			else
				current = current->getStaticLink();
		}
		throw runtime_error("Cannot find the variable " + variable);
	}

	//search for the value of the given variable
	VarEntry& RuntimeStack::lookup(string variable)
	{
		ActivationRecord	*current = &RTstack[RTstack.size()-1];
		int					level;	//level of current activation record
		int					plevel; //level of its parent activation record

		//Found in topmost AR
		if ( current->getMapping()->contains(variable) )
			return current->getMapping()->lookup(variable);

		//Not found in topmost AR, continue search on Parents, Grandparents ...
		while( current != NULL )
		{
			level = current->getNestingLevel();
			current = current->getStaticLink();
			if ( current == NULL )
				break;
			plevel = current->getNestingLevel();
			try {
				return current->getMapping()->lookup(variable, level-plevel);
			} catch (runtime_error e)
			{
				//don't need to do anything
			}
		}
		throw runtime_error("Cannot find the variable " + variable);
	}

	//start a new scope level in current activation record
	void RuntimeStack::beginScope()
	{
		RTstack[RTstack.size()-1].getMapping()->beginScope();
	}

	//ends a new scope level in current activation record
	void RuntimeStack::endScope()
	{
		RTstack[RTstack.size()-1].getMapping()->endScope();
	}
}
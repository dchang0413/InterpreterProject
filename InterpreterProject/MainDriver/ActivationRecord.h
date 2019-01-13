#pragma once
#include <string>
#include "SymbolTable.h"

using namespace std;

namespace runtime
{
	//In this implementation, only int or string variables 
	//are considered.
	struct VarEntry
	{
		enum ValueType {INT, STRING, VOID};

		ValueType	type;
		int		ival;	//integer value
		string	sval;	//string value

		VarEntry()
			: type(VOID)
		{}

		VarEntry(int i)
			: type(INT), ival(i), sval("")
		{}

		VarEntry(string s)
			: type(STRING), ival(-1), sval(s)
		{}

		bool isInt() { return type == INT; }
		bool isString() { return type == STRING; }
	};

	class ActivationRecord
	{
	public:
		ActivationRecord(ActivationRecord* l, symbol::SymTabEntry* r)
			: slink(l), routine(r)
		{
		}

		~ActivationRecord(void)
		{}

		int getNestingLevel() const;
		ActivationRecord * getStaticLink();
		const symbol::SymTabEntry* getRoutine() const;
		
		symbol::SymbolTable<VarEntry> * getMapping();

	private:
		symbol::SymbolTable<VarEntry>	mapping;	//map a variable to a value (either int or string)
		ActivationRecord				*slink;		//static link
		symbol::SymTabEntry				*routine;	//routine information
	};
}

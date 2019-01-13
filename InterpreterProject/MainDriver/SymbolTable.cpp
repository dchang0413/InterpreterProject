#include <iostream>
#include <sstream>

/*
PROGRAMMER: Paul Fleming
PROGRAM: project5
DUE DATE: 11/12/18
INSTRUCTOR: Dr. Zhijiang Dong
*/

//The insert and various contains functions were defined.

using namespace std;

namespace symbol
{

	//get the level of current scope
	template<class Entry>
	int SymbolTable<Entry>::getLevel() const
	{
		return level;
	}

	//Save the information of current scope to the string dumpinfo
	//It should be called at the beginning of the endScope function.
	template<class Entry>
	void SymbolTable<Entry>::dump()
	{
		int			level = tables.size();
		string		indent;
		HashTable	current = *(tables.begin());
		HashTable::iterator	it = current.begin();

		for (int i = 0; i<level; i++)
			indent += "    ";
		string			info;
		stringstream	ss(info);

		for (; it != current.end(); ++it)
			ss << indent << it->first << endl;
		ss << indent << "-------------------------------" << endl;
		dumpinfo += ss.str();
	}

	//to remove all scopes from the hashtable list so that
	//all remaining scopes will be dumped.
	template<class Entry>
	SymbolTable<Entry>::~SymbolTable()
	{
		//delete all remaining scopes 
		for (unsigned int i = 0; i<tables.size(); i++)
			endScope();

		//cout << "*******************Symbol Table************************" << endl;
		//cout << dumpinfo << endl;
		//cout << "*******************Symbol Table************************" << endl;
	}


	//Retrieve the value associated with the given lexeme in the hashtable list
	//search from the head to tail
	//an exception is thrown if the lexeme doesn't exist
	template<class Entry>
	Entry& SymbolTable<Entry>::lookup(string lexeme, int blevel)
	{
		if (blevel == -1)
			blevel = getLevel();
		//skip levels between blevel and getLevel()
		int skip = getLevel() - blevel;
		for (Iterator it = tables.begin(); it != tables.end(); it++)
		{
			//skip these levels
			if (skip > 0)
			{
				skip--;
				continue;
			}
			HashTable &current = *it;
			HashTable::iterator vit = current.find(lexeme);
			if (vit != current.end())
			{
				return current[lexeme]; //found the lexeme
			}
		}
		throw runtime_error("The given Lexeme " + lexeme + " doesn't exist!");
	}

	//Retrieve the value associated with the given lexeme in the global level only
	//an exception is thrown if the lexeme doesn't exist
	template<class Entry>
	Entry& SymbolTable<Entry>::globalLookup(string lexeme)
	{
		Iterator	prev;
		Iterator	cur = tables.begin();

		while (cur != tables.end())
		{
			prev = cur;
			cur++;
		}

		HashTable		&current = *prev;

		if (current.find(lexeme) != current.end())
		{
			return current[lexeme];	//found the lexeme
		}
		throw runtime_error("The given Lexeme " + lexeme + " doesn't exist!");
	}

	//create a new scope as the current scope
	template<class Entry>
	void SymbolTable<Entry>::beginScope()
	{
		level++;
		tables.push_front(HashTable());
	}

	//destroy the current scope, and its parent becomes the current scope
	template<class Entry>
	void SymbolTable<Entry>::endScope()
	{
		dump();

		//remove current scope level from the symbol table
		if (level >= 0)
		{
			tables.pop_front();
			level--;
		}
	};

	/****************************
	Provide implementation of all other member functions here
	****************************/

	//check if a lexeme is contained in the symbol table list
	//search from the head to tail
	template<class Entry>
	bool SymbolTable<Entry>::contains(string lexeme)
	{
		for (Iterator it = tables.begin(); it != tables.end(); it++)
		{
			HashTable		&current = *it;
			HashTable::iterator	vit = current.find(lexeme);

			if (vit != current.end())
			{
				return true;	//found the lexeme
			}
		}
		return false;
	}


	template<class Entry>
	bool SymbolTable<Entry>::localContains(string lexeme)
	{
		Iterator it = tables.begin();
		HashTable &current = *it;

		if (current.find(lexeme) != current.end())
		{
			return true;	//found the lexeme
		}
		return false;
	}

	//check if a lexeme is contained in the global level
	template<class Entry>
	bool SymbolTable<Entry>::globalContains(string lexeme)
	{
		HashTable current = *(tables.end());
		HashTable::iterator it = current.begin();

		for (; it != current.end(); it++)
		{
			if (it->first == lexeme)
			{
				return true;	//found the lexeme
			}
		}
		return false;
	}

	//insert a lexeme and binder to the current scope, i.e. the first hashtable in the list
	//if it exists, an exception will be thrown
	template<class Entry>
	void SymbolTable<Entry>::insert(string lexeme, const Entry value)
	{
		//first check to make sure this is not a dup
		if (localContains(lexeme))
			throw runtime_error("The given Lexeme " + lexeme + " already exists!");

		//if not then insert the lexeme with the binder entry
		else
		{
			Iterator it = tables.begin();
			it->insert({ lexeme, value });
		}
	}

} //end of namespace Environment




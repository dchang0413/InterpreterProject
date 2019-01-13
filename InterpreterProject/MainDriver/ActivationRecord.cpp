#include "ActivationRecord.h"

namespace runtime
{
	int ActivationRecord::getNestingLevel() const
	{
		if ( slink == NULL )
			return 0;
		else
			return routine->level;
	}

	symbol::SymbolTable<VarEntry> * ActivationRecord::getMapping()
	{
		return &mapping;
	}
	
	ActivationRecord * ActivationRecord::getStaticLink()
	{
		return slink;
	}
	
	const symbol::SymTabEntry* ActivationRecord::getRoutine() const
	{
		return routine;
	}
}
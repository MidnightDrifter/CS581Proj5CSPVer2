#include "csp.h"
#ifdef INLINE_CSP
	//#warning "INFO - inlining CSP methods"
	#define INLINE inline
#else   
	//#warning "INFO - NOT inlining CSP methods"
	#define INLINE 
#endif

////////////////////////////////////////////////////////////
//CSP constructor
template <typename T> 
CSP<T>::CSP(T &cg) :
	arc_consistency(),
	cg(cg),
	solution_counter(0),
	recursive_call_counter(0),
	iteration_counter(0) 
{
}

////////////////////////////////////////////////////////////
//CSP solver, brute force - no forward checking
template <typename T> 
bool CSP<T>::SolveDFS(unsigned level) {
	++recursive_call_counter;
	//std::cout << "entering SolveDFS (level " << level << ")\n";


	//Place base case before or after this counter??

	if (cg.AllVariablesAssigned())
	{
		return true;
	}


    
	
	
	//choose a variable by MRV
	Variable* var_to_assign = MinRemVal();
	//Variable* var_to_assign = MaxDegreeHeuristic();


	if (!var_to_assign || var_to_assign->SizeDomain()==0)
	{
		return false;   //Something has gone wrong
	}





    //loop(... )

	for (auto varRangeIter = var_to_assign->GetDomain().begin(); varRangeIter != var_to_assign->GetDomain().end(); varRangeIter++)
	{
	


        ++iteration_counter;




		//For each value in var_to_assign
			//Try and assign it to var
			//If it breaks a constraint, unassign & move to next iteration
			//Otherwise, return SolveDFS(level + 1)
		//If NO values work, return false--this branch won't work


		Variable varCopy = *var_to_assign;

		var_to_assign->Assign(*varRangeIter);

		//Assignment doesn't work, try again
		if (!(this->AssignmentIsConsistent(var_to_assign)))
		{
			var_to_assign->UnAssign();
			*var_to_assign = varCopy;
		}

		else
		{
			
			return SolveDFS(level + 1);
		}
			
	

    }



	return false;
}


////////////////////////////////////////////////////////////
//CSP solver, uses forward checking
template <typename T> 
bool CSP<T>::SolveFC(unsigned level) {
	++recursive_call_counter;
	//std::cout << "entering SolveFC (level " << level << ")\n";

	if (cg.AllVariablesAssigned())
	{
		return true;
	}
	
    
    //choose a variable by MRV
	Variable* var_to_assign = MinRemVal();
	//Variable* var_to_assign = MaxDegreeHeuristic();

	if (!var_to_assign || var_to_assign->SizeDomain() == 0)
	{
		return false;   //Something has gone wrong
	}



	//Save variable states
	//If var_to_assign's domain is EMPTY, return false

	std::map<Variable*, std::set<typename Variable::Value> > state = this->SaveState(var_to_assign);

    //loop( ... ) {
	for (auto varRangeIter = var_to_assign->GetDomain().begin(); varRangeIter != var_to_assign->GetDomain().end(); varRangeIter++)
	{
        ++iteration_counter;

		//Try to assign value to x
		//Check forward checking--don't need to save this value, forward checking SHOULD handle the saving & reverting on its own
		Variable varCopy = *var_to_assign;
		var_to_assign->Assign(*varRangeIter);
		if (ForwardChecking(var_to_assign) && AssignmentIsConsistent(var_to_assign))  //Forward checking should take care of the consistent bit, but just in case...
		{
			return SolveFC(level + 1);
		}

		else
		{
			var_to_assign->UnAssign();
			*var_to_assign = varCopy;
			this->LoadState(state);
		}
    }

	return false;


}
////////////////////////////////////////////////////////////
//CSP solver, uses arc consistency
template <typename T> 
bool CSP<T>::SolveARC(unsigned level) {
	++recursive_call_counter;
	//std::cout << "entering SolveARC (level " << level << ")\n";

	
	if (cg.AllVariablesAssigned())
	{
		return true;
	}

    
    
    //choose a variable by MRV
	Variable* var_to_assign = MinRemVal();
    
    
	if (!var_to_assign || var_to_assign->SizeDomain() == 0)
	{
		return false;   //Something has gone wrong
	}


	std::map<Variable*, std::set<typename Variable::Value> > state = this->SaveState(var_to_assign);






    
    //loop( ... ) {
	for (auto varRangeIter = var_to_assign->GetDomain().begin(); varRangeIter != var_to_assign->GetDomain().end(); varRangeIter++)
	{
        ++iteration_counter;

		Variable varCopy = *var_to_assign;

		var_to_assign->Assign(*varRangeIter);

		if (CheckArcConsistency(var_to_assign) && AssignmentIsConsistent(var_to_assign))
		{
			return SolveARC(level + 1);
		}

		else
		{
			var_to_assign->UnAssign();
			*var_to_assign = varCopy;
			this->LoadState(state);
		}


    }

	return false;

}


template <typename T> 
INLINE
bool CSP<T>::ForwardChecking(Variable *x) {

	//Only inserts if this will NOT make the problem impossible--i.e. it reduces the number of values in a given variable's range to 0


	//For each neighbor variable in constraint graph:
		//Get set of constraints that involve that variable & the input var
		//Check these constraints for solvability
			//if ANY constraint is unsolvable, cannot assign this variable, abort and break, revert changes, return false


	//If we get out of the loop successfully, the assignment is ok, return true



	//std::vector<const Constraint*>& tempConstraints = cg.
	const std::set<Variable*>& neighbors = cg.GetNeighbors(x);
	// = nullptr;     // , *constraintsCopy = NULL;
	Constraint* constraintCopy = NULL;
	for (auto i = neighbors.begin(); i != neighbors.end(); i++)
	{
		const std::set<const Constraint*>& connectingConstraints = cg.GetConnectingConstraints(x, (*i));
		//  *constraintsCopy = *connectingConstraints;


		
			for (auto j = connectingConstraints.begin(); j != connectingConstraints.end(); j++)
			{
				constraintCopy = (*j)->clone();
				constraintCopy->AddVariable(x);



				if (!constraintCopy->Satisfiable())
				{
					//delete temp;
					delete constraintCopy;
					constraintCopy = nullptr;
					return false;
				}

				else
				{
					delete constraintCopy;
					constraintCopy = nullptr;
				}






			}


		
	}


	//Got out of the loop, assignment is OK--get rid of the temporary & assign the variable into the ACTUAL constraint graph array
	//connectingConstraints = nullptr;
	//this->cg.InsertVariable(x);
	/*
	for (auto i = neighbors.begin(); i != neighbors.end(); i++)
	{
		connectingConstraints = cg.GetConnectingConstraints(x, *i);
		//   *constraintsCopy = *connectingConstraints;


		if (connectingConstraints)
		{
			for (auto j = connectingConstraints->begin(); j != connectingConstraints->end(); j++)
			{
				(*j)->AddVariable(x);
			}
		}
	}
	*/



	return true;



}
////////////////////////////////////////////////////////////
//load states (available values) of all unassigned variables 
template <typename T> 
void CSP<T>::LoadState(
		std::map<Variable*, 
		std::set<typename CSP<T>::Variable::Value> >& saved) const 
{
	typename std::map<Variable*, std::set<typename Variable::Value> >::iterator 
		b_result = saved.begin();
	typename std::map<Variable*, std::set<typename Variable::Value> >::iterator 
		e_result = saved.end();

	for ( ; b_result != e_result; ++b_result ) {
		//std::cout << "loading state for " 
		//<< b_result->first->Name() << std::endl;
		(*b_result).first->SetDomain( (*b_result).second );
	}
}


////////////////////////////////////////////////////////////
//save states (available values) of all unassigned variables 
//except the current
template <typename T> 
INLINE
std::map< typename CSP<T>::Variable*, std::set<typename CSP<T>::Variable::Value> > 
CSP<T>::SaveState(typename CSP<T>::Variable* x) const {
	std::map<Variable*, std::set<typename Variable::Value> > result;

	const std::vector<Variable*>& all_vars = cg.GetAllVariables();
	typename std::vector<Variable*>::const_iterator 
		b_all_vars = all_vars.begin();
	typename std::vector<Variable*>::const_iterator 
		e_all_vars = all_vars.end();
	for ( ; b_all_vars!=e_all_vars; ++b_all_vars) {
		if ( !(*b_all_vars)->IsAssigned() && *b_all_vars!=x ) {
			//std::cout << "saving state for " 
			//<< (*b_all_vars)->Name() << std::endl;
			result[ *b_all_vars ] = (*b_all_vars)->GetDomain();
		}
	}
	return result;
}
////////////////////////////////////////////////////////////
//check the current (incomplete) assignment for satisfiability
template <typename T> 
INLINE
bool CSP<T>::AssignmentIsConsistent( Variable* p_var ) const {




	for (auto constraintIter = cg.GetConstraints(p_var).begin(); constraintIter != cg.GetConstraints(p_var).end(); constraintIter++)
	{
		Constraint* temp = (*constraintIter)->clone();
		
		temp->AddVariable(p_var);
		if (!temp->Satisfiable())
		{
			delete temp;  //Check if this deletes all the variables inside it!!
			return false;
		}

		delete temp;   //Check if this deletes all the variables inside it!!
	}


	return true;


}
////////////////////////////////////////////////////////////
//insert pair 
//(neighbors of the current variable, the current variable)
//current variable is the variable that just lost some values
// for all y~x insert (y,x)
//into arc-consistency queue
template <typename T> 
INLINE
void CSP<T>::InsertAllArcsTo( Variable* cv ) {



	//for each neighbor of cv
		//for each constraint connecting cv & current neighbor
			//push back into arc-consistency queue




	for (auto neighborIter = cg.GetNeighbors(cv).begin(); neighborIter != cg.GetNeighbors(cv).end(); neighborIter++)
	{
		for (auto constraintIter = cg.GetConnectingConstraints(*neighborIter, cv).begin(); constraintIter != cg.GetConnectingConstraints(*neighborIter, cv).end(); constraintIter++)
		{

			this->arc_consistency.emplace(*neighborIter, cv, *constraintIter);



		}
	
	
	}







}
////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////
//AIMA p.146 AC-3 algorithm
template <typename T> 
INLINE
bool CSP<T>::CheckArcConsistency(Variable* x) {



	//while arc queue isn't empty:
		//testArc = arc_queue.top, pop
		//if(remove inconsistent values)
			//for each neighbor


	//Assuming x has been assigned to already


	Variable xCopy = *x;

	//Potentially save all variables out here
	//Actually, we'll probably NEED to save them out here.  I think


	while (!(this->arc_consistency.empty()))
	{
	//	Arc<Constraint> arc = *(this->arc_consistency).begin();
	//	(this->arc_consistency).erase((this->arc_consistency).begin());

		for (auto yIterator = cg.GetNeighbors(x).begin(); yIterator != cg.GetNeighbors(x).end(); yIterator++)
		{
			for (auto constraintIter = cg.GetConnectingConstraints(x, *yIterator).begin(); constraintIter != cg.GetConnectingConstraints(x, *yIterator).end(); constraintIter++)
			{

				//IF we remove values, we gotta check all the new arcs we just made
				//IF X ever runs out of values, we now know it's not satisfiable, return FALSE

				
				if (!(*constraintIter)->Satisfiable() || x->SizeDomain() == 0)
				{
					if (x->IsAssigned())
					{
						x->UnAssign();
					}

					if ((*yIterator)->IsAssigned())
					{
						(*yIterator)->UnAssign();
					}


					*x = xCopy;
					//Potentially load all variables in here
					return false;

				}



				if (this->RemoveInconsistentValues(x, *yIterator, *constraintIter))
				{
					this->InsertAllArcsTo(x);
				}






			}




		}
	}

	return false;
}
////////////////////////////////////////////////////////////
//CHECK that for each value of x there is a value of y 
//which makes all constraints involving x and y satisfiable


//Do I actually go through and remove the values that are inconsistent, or just check for them here??

template <typename T> 
INLINE
bool CSP<T>::RemoveInconsistentValues(Variable* x,Variable* y,const Constraint* c) {

/*
	bool out = false;

	Constraint* temp = c->clone();
	temp->AddVariable(x);
	temp->AddVariable(y);   //Check if the Constraint destructor deletes the variables inside it!

	if (temp)
	{
		out = temp->Satisfiable();
		delete temp;   //Check if this deletes vars inside it!
	}

	if (out)
	{
		
		c->AddVariable(x);
			c->AddVariable(y);
	}
	return out;






	*/

//Returns true if values were removed successfully -- removing values from X

	bool out = false;

	Constraint* constraintTemp = nullptr;  // c->clone();
	//Variable* yTemp = y->clone();
	//Variable* xCopy = y->clone();


	//for each value of X
		//Constraint = constraint->clone()
		//Variable testX = Variable(that value of X) & assign its value
		//Push into constraint
		//if constraint isn't satisfiable
			//Remove value from X
			//Set out to 'true' -- values have been removed!
		
	
	for (auto valIterator = x->GetDomain().begin(); valIterator != x->GetDomain().end(); valIterator++)
	{
		x->Assign(*valIterator);	
		bool satisfiable = false;
		for (auto yIterator = y->GetDomain().begin(); yIterator != y->GetDomain().end(); )
		{
			y->Assign(*yIterator);
			constraintTemp = c->clone();
			//bool satisfiable = false;
			constraintTemp->AddVariable(x);
			constraintTemp->AddVariable(y);
			if (constraintTemp->Satisfiable())
			{
			
				yIterator = y->GetDomain().end();
		
				satisfiable = true;
			}


			else
			{
				
				yIterator++;
			}
			y->UnAssign();
			delete constraintTemp;
			constraintTemp = nullptr;


		}


		if (!satisfiable)
		{
			x->RemoveValue(*valIterator);

			out = true;
		}

		x->UnAssign();

	}


	return out;


}
////////////////////////////////////////////////////////////
//choose next variable for assignment
//choose the one with minimum remaining values
template <typename T> 
INLINE
typename CSP<T>::Variable* CSP<T>::MinRemVal() {




	auto i = cg.GetAllVariables().begin();

	CSP<T>::Variable* out = *i;   //If there are no variables, something will go wrong here most likely

	for ( ; i != cg.GetAllVariables().end(); i++)
	{
		
		if (out->SizeDomain() > (*i)->SizeDomain())
		{
			out = *i;
		}
		

	}

	return out;





}
////////////////////////////////////////////////////////////
//choose next variable for assignment
//choose the one with max degree
template <typename T> 
typename CSP<T>::Variable* CSP<T>::MaxDegreeHeuristic() {






	//Choose variable that touches the MOST constraints
	//Vars don't know about constraints, but constraints know about vars

	//Variable* out = nullptr;


	std::pair<Variable*, int> temp(nullptr, 0);

	for (auto varIter = cg.GetAllVariables.begin(); varIter != cg.GetAllVariables.end(); varIter++)
	{
		if (cg.GetConstraints(*varIter).size() > temp.second)
		{
			temp.first = *varIter;
			temp.second = cg.GetConstraints(*varIter);
		}
	}


	return temp.first;





}
#undef INLINE

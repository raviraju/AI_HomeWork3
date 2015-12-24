#include <iostream>		//cout
#include <fstream>		//ifstream,ofstream
#include <sstream>
#include <string>		//string
#include <cstring> 		//strncmp
#include <cstdlib>		//atoi
#include <algorithm> 	//remove
#include <vector> 		//tokenize
#include <list> 		//list of args of Predicate
#include <utility> 		//pair
#include <map>			//KB
#include <set>			//variables
#include <sstream>		//stringstream

using namespace std;

typedef list <string>::iterator listStringsItr;

template <typename Map>
bool map_compare (Map const &lhs, Map const &rhs) {
    // No predicate needed because there is operator== for pairs already.
    return lhs.size() == rhs.size()
        && std::equal(lhs.begin(), lhs.end(),
                      rhs.begin());
}

class predicate
{
	string name;
	list<string> arguments;
	set<string> variables;
	bool isVariable(string arg)//return true if argument is variable
	{
		//variable : start with lwr case
		//Constants : case-sensitive strings, begin with Cap
		if( (islower(arg.at(0)) != 0) )
			return true;
		else
			return false;
	}
public:
	predicate(){}
	predicate(string n, list <string>& args):name(n),arguments(args)
	{
		//cout << n << " ";
		for(listStringsItr it = args.begin(); it != args.end(); ++it)
		{
			if(isVariable(*it))
			{
				variables.insert(*it);
				//cout << *it << " is a variable" << variables.size() << endl;
			}
		}
	}
	predicate(const predicate& rhs):name(rhs.name),arguments(rhs.arguments),variables(rhs.variables){}//copy ctor
	void display()
	{
		cout << name <<"(";
		for(listStringsItr it = arguments.begin(); it != arguments.end(); ++it)
		{
			cout << " " << (*it) << ","; 
		}
		cout << ") ";
		//displayVariables();
	}
	void displayVariables()
	{
		cout << " Variables : " << variables.size();
		for(set<string>::iterator it = variables.begin(); it != variables.end(); ++it)
		{
			cout << " " << (*it) << ","; 
		}
	}
	string getName()
	{
		return name;
	}
	void setName(string n)
	{
		name = n;
	}
	list<string>& getArgs()
	{
		return arguments;
	}
	set<string> getVariables()
	{
		return variables;
	}
};

bool isVariable(string arg)//return true if argument is variable
{
	//variable : single lwr case
	//Constants : case-sensitive strings, begin with Cap
	if( (islower(arg.at(0)) != 0) )
		return true;
	else
		return false;
}
	

typedef list<predicate> predicateList;
typedef predicateList::iterator predicateListItr;

map<string,int> globalVarMap;
typedef map<string,int>::iterator globalVarMapItr;

predicate* renamePredicate(predicate& old,map<string, string>& rMap);

class rule
{
	predicateList premises;
	predicate conclusion;
	set<string> variables;
public:
	rule(predicateList& givenPremises,predicate& givenConcl)//	:premises(givenPremises),conclusion(givenConcl)
	{
		for(predicateListItr it = givenPremises.begin(); it != givenPremises.end(); ++it)
		{
			set<string> premise_vars = it->getVariables();
			for(set<string>::iterator pv = premise_vars.begin(); pv != premise_vars.end(); ++pv)
			{
				variables.insert(*pv);
			}
		}
		set<string> conclusion_vars = givenConcl.getVariables();
		for(set<string>::iterator cv = conclusion_vars.begin(); cv != conclusion_vars.end(); ++cv)
		{
			variables.insert(*cv);
		}
		
		map<string, string> replaceMap;
		for(set<string>::iterator it = variables.begin(); it != variables.end(); ++it)
		{
			string var = *it;
			globalVarMapItr varMapItr = globalVarMap.find(var);
			if(varMapItr == globalVarMap.end())//not_found, new var
			{
				globalVarMap[var] = 1;
				replaceMap[var] = var;
			}
			else
			{
				stringstream out;
				out << globalVarMap[var];
				replaceMap[var] = var + string(out.str());
				globalVarMap[var]++;
			}
		}
		map<string, string>::iterator replaceMapItr;
		/*cout << "replaceMap : " << endl;
		for(replaceMapItr = replaceMap.begin(); replaceMapItr != replaceMap.end(); ++replaceMapItr)
		{
			cout << "replace : " << replaceMapItr->first << " with " << replaceMapItr->second << endl; 
		}*/
		if(replaceMap.empty())
		{
			premises = givenPremises;
			conclusion = givenConcl;
		}
		else
		{
			//premises = givenPremises;
			//conclusion = givenConcl;
			
			predicateList new_premises;
			for(predicateListItr premiseIt = givenPremises.begin(); premiseIt != givenPremises.end(); ++premiseIt)
			{
				predicate* new_premise = renamePredicate((*premiseIt), replaceMap);
				new_premises.push_back(*new_premise);
			}
			predicate* new_conclusion = renamePredicate(givenConcl, replaceMap);
			
			premises = new_premises;
			conclusion = *new_conclusion;
		}
		
		
		
	}
	void display()
	{
		for(predicateListItr it = premises.begin(); it != premises.end(); ++it)
		{
			cout << " ";
			(*it).display();
			cout << "^"; 
		}
		if(!isFact())
			cout << " => ";
		conclusion.display();
		/*cout << " has Variables : ";
		for(set<string>::iterator it = variables.begin(); it != variables.end(); ++it)
		{
			cout << " " << (*it) << ","; 
		}*/
		cout << endl;
	}
	predicate* getConclusion()
	{
		return &conclusion;
	}
	predicateList* getPremises()
	{
		return &premises;
	}
	bool isFact()
	{
		if (premises.size() == 0)
			return true;
		else
			return false;
	}
};
typedef list<rule> ruleList;
typedef ruleList::iterator ruleListItr;

map<string, ruleList > KB;
map<string, ruleList > orderedKB;
typedef map<string, ruleList >::iterator kb_itr;

//map<string, list<string> > historyOfGoals;
//typedef map<string, list<string> >::iterator historyOfGoalsItr;

typedef map<string,string> substitutionMap;
typedef map<string,string>::iterator substitutionMapItr;

map<list<string>,list<substitutionMap> > newHistoryOfGoals;
typedef map<list<string>,list<substitutionMap> >::iterator newHistoryOfGoalsItr; 


void displayKB()
{
	cout << "================================================================================"<<endl;
	cout << "Predicate					Rules"<<endl;
	for(kb_itr it = KB.begin(); it != KB.end(); ++it)
	{
		cout << it->first << endl;
		ruleList& rules = it->second;
		//cout << "\t\t\t Rules : " << rules.size() << endl;
		for (ruleListItr rl_Itr = rules.begin(); rl_Itr != rules.end(); rl_Itr++)
		{
			cout << "\t\t\t\t\t";
			if(rl_Itr->isFact())
				cout << "Fact : ";
			rl_Itr->display();
			
		}
	}
	cout << "================================================================================"<<endl;
}

void displayOrderedKB()
{
	cout << "================================================================================"<<endl;
	cout << "Predicate					Rules"<<endl;
	for(kb_itr it = orderedKB.begin(); it != orderedKB.end(); ++it)
	{
		cout << it->first << endl;
		ruleList& rules = it->second;
		//cout << "\t\t\t Rules : " << rules.size() << endl;
		for (ruleListItr rl_Itr = rules.begin(); rl_Itr != rules.end(); rl_Itr++)
		{
			cout << "\t\t\t\t\t";
			if(rl_Itr->isFact())
				cout << "Fact : ";
			rl_Itr->display();
			
		}
	}
	cout << "================================================================================"<<endl;
}

//facts are preceded by rules
void orderRulesKB()
{
	for(kb_itr it = KB.begin(); it != KB.end(); ++it)
	{
		ruleList factRules;
		ruleList actualRules;
		ruleList orderedRules;
		
		ruleList& rules = it->second;
		for (ruleListItr rl_Itr = rules.begin(); rl_Itr != rules.end(); rl_Itr++)
		{
			if(rl_Itr->isFact())
			{
				factRules.push_back(*rl_Itr);
			}
			else
			{
				actualRules.push_back(*rl_Itr);
			}
		}
		
		for (ruleListItr rl_Itr = factRules.begin(); rl_Itr != factRules.end(); rl_Itr++)
		{
			orderedRules.push_back(*rl_Itr);
		}
		for (ruleListItr rl_Itr = actualRules.begin(); rl_Itr != actualRules.end(); rl_Itr++)
		{
			orderedRules.push_back(*rl_Itr);
		}
		orderedKB[it->first] = orderedRules;
	}
}

string removeSpaces(string input)
{
	input.erase(remove(input.begin(),input.end(),' '),input.end());
	return input;
}

void tokenize(list <string>& tokens, string source, char delimiter)
{
	std::string  temp;
	while (source.find(delimiter, 0) != std::string::npos)
	{ //does the string a delimiter in it?
		size_t pos = source.find(delimiter, 0); //store the position of the delimiter
		temp = source.substr(0, pos);      		//get the token
		source.erase(0, pos + 1);          		//erase it from the source 
		tokens.push_back(temp);                	//and put it into the array
	}
	tokens.push_back(source);           		//the last token is all alone 
}

//P(x,y,z); Brother(Richard,John); ~H(Alice)
predicate* parsePredicate(string predicateStr)
{
	std::size_t parenthesisPos =predicateStr.find("(");
	if(parenthesisPos != string::npos)
	{
		string name = predicateStr.substr (0,parenthesisPos);
		predicateStr.erase(0,parenthesisPos+1);//remove name part
		string argsStr = predicateStr.substr (0,predicateStr.size()-1);//exclude '(' and ')'
		//cout << "Predicate Name : " << name << " ArgsStr : " << argsStr;
		list <string> args;
		tokenize(args,argsStr,',');
		//cout << "Arguments : ";
		/*for(listStringsItr it = args.begin(); it != args.end(); ++it)
		{
			cout << " " << *it ; 
		}*/
		return new predicate(name,args);
	}
	else
		cout << "Invalid Predicate : " << predicateStr << endl;

}


//Enemy(x,America)-->Enemy(x1,America)
predicate* renamePredicate(predicate& old,map<string, string>& rMap)
{
	string new_name = old.getName();
	list<string>& oldArgs = old.getArgs();
	list<string> newArgs;
	for(listStringsItr it_old = oldArgs.begin(); it_old != oldArgs.end(); ++it_old)
	{
		string old_arg = *it_old;
		string new_arg = old_arg;
		if(isVariable(old_arg))
		{
			//if var is in replaceMap, use the new variable, else use same variable
			map<string, string>::iterator rMapItr = rMap.find(old_arg);
			if(rMapItr != rMap.end())
			{
				new_arg = rMapItr->second;
			}
		}
		newArgs.push_back(new_arg);
	}
	return new predicate(new_name,newArgs);
}

//P(x,y,z); Brother(Richard,John); ~H(Alice)
rule* parsePredicateAsRule(string predicateStr)
{
	predicateList empty_antecedent;
	predicate* consequent = parsePredicate(predicateStr);
	return new rule(empty_antecedent,*consequent);
}

rule* parseRule(string ruleStr,size_t impPos)
{
	string premise = ruleStr.substr (0,impPos); 
	//DEBUG cout << "Premise : " << premise << endl;
	//get rid of spaces
	list <string> conjucts;
	tokenize(conjucts, removeSpaces(premise), '^');
	predicateList antecedent;
	for(listStringsItr it = conjucts.begin(); it != conjucts.end(); ++it)
	{
		//cout << " " << *it ;
		predicate* conjunct = parsePredicate(*it);
		antecedent.push_back(*conjunct);
	}
	string concl = ruleStr.substr (impPos+4); 
	//DEBUG cout << "\nConclusion : " << concl << endl;
	predicate* consequent = parsePredicate(concl);
	string key = consequent->getName();
	return new rule(antecedent,*consequent);	
}

//Knows(John,x), Knows(John,Jane) 	= {x/Jane}
//Knows(John,x), Knows(y,Bill) 		= {y/John,x/Bill}
//Knows(John,x), Knows(x,Elizabeth)
//Standardize : Knows(John,x), Knows(y,Elizabeth) = {y/John,x/Elizabeth}
//Knows(John,x), Knows(y,Mother(y)) = {y/John,x/Mother(John)}-------------------NOT REQ to handle
bool unify(predicate& p1,predicate& p2,substitutionMap& theta)
{
	cout << "Unification of "; p1.display(); cout << "with "; p2.display(); 
	if(p1.getName() != p2.getName())//predicate names dont match, useful when we try to unify with each of conjunts of a rule
	{
		cout << " is : FAIL (predicate names dont match)" << endl;
		return false;
	}
	list<string>& p1_args = p1.getArgs();
	list<string>& p2_args = p2.getArgs();
	//check for no of args mismatch
	if(p1_args.size() != p2_args.size())
	{
		cout << " is : FAIL (predicate no of args mismatchh)" << endl;
		return false;
	}
	//compare arguments and build substitution for variables
	listStringsItr p1_args_itr = p1_args.begin();
	listStringsItr p2_args_itr = p2_args.begin();
	//Knows(x,y), Knows(John,Jane) 	= {x/John,y/Jane} true
	//Knows(x,y,x), Knows(John,Bill,Jane) 	= {x/John,y/Bill,x/Jane} false same variable with different values
	//B(John,y), B(John,Bob) = {y/Bob} true
	//D(x,John), D(John,Alice) = {x/John John/Alice} cant unify two different constants
	//D(x,John), D(John/Bob)   = {x/John John/Bob} cant unify two different constants
	for(	;(p1_args_itr!=p1_args.end()) or (p2_args_itr!=p2_args.end()) ; ++p1_args_itr, ++p2_args_itr)
	{
		string arg1 = *p1_args_itr;
		string arg2 = *p2_args_itr;
		//BOTH ARGS are Constants, there should be perfect match, if not break
		if(!isVariable(arg1) && !isVariable(arg2))
		{
			if(arg1 != arg2)
			{
				//B(John,y), B(Ravi,Bob) = {John/Ravi y/Bob} false
				cout << " is : FAIL (corresponding constants dont match)" << endl;
				return false;
			}
			//B(John,y), B(John,Bob) = {y/Bob}
			continue;//process the next set of corresponding args
		}
		//IF first_arg is variable and second_arg is Constant
		else if(isVariable(arg1) && !isVariable(arg2))
		{
			//check if variable (arg1) already has any assignment in map substitutionMap:theta
			substitutionMapItr it = theta.find(arg1);
			if(it != theta.end())//exisiting substitution found
			{
				//if the existing substitution is same as arg2(Fact)....No issues, hence proceed with next set of args
				if(it->second == arg2)
				{
					//Knows(x,y,x), Knows(John,Jane,x) 	= {x/John,y/Jane}
					continue;//process the next set of corresponding args
				}
				else
				{
					//Knows(x,y,x), Knows(John,Bill,Jane) 	= {x/John,y/Bill,x/Jane} false same variable with different values
					//conflicting Facts for the same variable, cant unify
					cout << " is : FAIL (conflicting Facts for the same variable)" << endl;
					return false;
				}
			}
			else// no exisiting substitution for variable arg1, so add new substitution
			{
				//Knows(x,y), Knows(John,Jane) 	= {x/John,y/Jane}
				theta[arg1] = arg2;
				continue;//process the next set of corresponding args
			}
		}
		//IF first_arg is Constant and second_arg is variable
		else if(!isVariable(arg1) && isVariable(arg2))
		{
			//check if variable (arg2) already has any assignment in map substitutionMap:theta
			substitutionMapItr it = theta.find(arg2);
			if(it != theta.end())//exisiting substitution found
			{
				//if the existing substitution is same as arg1(Fact)....No issues, hence proceed with next set of args
				if(it->second == arg1)
				{
					continue;//process the next set of corresponding args
				}
				else
				{
					//conflicting Facts for the same variable, cant unify
					cout << " is : FAIL (conflicting Facts for the same variable)" << endl;
					return false;
				}
			}
			else// no exisiting substitution for variable arg1, so add new substitution
			{
				theta[arg2] = arg1;
				continue;//process the next set of corresponding args
			}
		}
		//BOTH ARGS are variables
		else
		{
			cout << "arg2 : " << arg2 << " arg1 : " << arg1 << endl;
			//cout << " is : FAIL (BOTH ARGS are variables!!!!!!!!!!!!!FIGURE OUT HOW TO HANDLE)" << endl;
			//return false;
			
			//check if variable (arg2) already has any assignment in map substitutionMap:theta
			substitutionMapItr it = theta.find(arg2);
			if(it != theta.end())//exisiting substitution found
			{
				//if the existing substitution is same as arg2(variable)....No issues, hence proceed with next set of args
				if(it->second == arg1)
				{
					//Knows(x,y,x), Knows(x1,y,x1)
					continue;//process the next set of corresponding args
				}
				else
				{
					//Knows(x,y,x), Knows(x1,y,x2)
					//conflicting Facts for the same variable, cant unify
					cout << " is : FAIL (conflicting variables for the same variable)" << endl;
					return false;
				}
			}
			else// no exisiting substitution for variable arg1, so add new substitution
			{
				//Knows(x,y), Knows(x1,y1)
				theta[arg2] = arg1;
				continue;//process the next set of corresponding args
			}
		}
	}
	cout << " is : PASS (with subst)";
	//cout << "******************************" << endl;
	//cout << "Variable\tSubstituion" << endl;
	//cout << "==============================" << endl;
	cout << " theta = { ";
	for(substitutionMapItr itr = theta.begin(); itr != theta.end(); ++itr)
	{
		cout << itr->first << "/" << itr->second << "  ";
	}
	cout << "}" << endl;
	//cout << "******************************" << endl;
	return true;
}

bool tryUnify(predicate& p1,predicate& p2,substitutionMap& theta)
{
	cout << "Trying Unification of "; p1.display(); cout << "with "; p2.display(); 
	if(p1.getName() != p2.getName())//predicate names dont match, useful when we try to unify with each of conjunts of a rule
	{
		cout << " is : FAIL (predicate names dont match)" << endl;
		return false;
	}
	list<string>& p1_args = p1.getArgs();
	list<string>& p2_args = p2.getArgs();
	//check for no of args mismatch
	if(p1_args.size() != p2_args.size())
	{
		cout << " is : FAIL (predicate no of args mismatchh)" << endl;
		return false;
	}
	//compare arguments and build substitution for variables
	listStringsItr p1_args_itr = p1_args.begin();
	listStringsItr p2_args_itr = p2_args.begin();
	//Knows(x,y), Knows(John,Jane) 	= {x/John,y/Jane} true
	//Knows(x,y,x), Knows(John,Bill,Jane) 	= {x/John,y/Bill,x/Jane} false same variable with different values
	//B(John,y), B(John,Bob) = {y/Bob} true
	//D(x,John), D(John,Alice) = {x/John John/Alice} cant unify two different constants
	//D(x,John), D(John/Bob)   = {x/John John/Bob} cant unify two different constants
	for(	;(p1_args_itr!=p1_args.end()) or (p2_args_itr!=p2_args.end()) ; ++p1_args_itr, ++p2_args_itr)
	{
		string arg1 = *p1_args_itr;
		string arg2 = *p2_args_itr;
		//BOTH ARGS are Constants, there should be perfect match, if not break
		if(!isVariable(arg1) && !isVariable(arg2))
		{
			if(arg1 != arg2)
			{
				//B(John,y), B(Ravi,Bob) = {John/Ravi y/Bob} false
				cout << " is : FAIL (corresponding constants dont match)" << endl;
				return false;
			}
			//B(John,y), B(John,Bob) = {y/Bob}
			continue;//process the next set of corresponding args
		}
		//IF first_arg is variable and second_arg is Constant
		else if(isVariable(arg1) && !isVariable(arg2))
		{
			//check if variable (arg1) already has any assignment in map substitutionMap:theta
			substitutionMapItr it = theta.find(arg1);
			if(it != theta.end())//exisiting substitution found
			{
				//if the existing substitution is same as arg2(Fact)....No issues, hence proceed with next set of args
				if(it->second == arg2)
				{
					//Knows(x,y,x), Knows(John,Jane,x) 	= {x/John,y/Jane}
					continue;//process the next set of corresponding args
				}
				else
				{
					//Knows(x,y,x), Knows(John,Bill,Jane) 	= {x/John,y/Bill,x/Jane} false same variable with different values
					//conflicting Facts for the same variable, cant unify
					cout << " is : FAIL (conflicting Facts for the same variable)" << endl;
					return false;
				}
			}
			else// no exisiting substitution for variable arg1, so add new substitution
			{
				//Knows(x,y), Knows(John,Jane) 	= {x/John,y/Jane}
				theta[arg1] = arg2;
				continue;//process the next set of corresponding args
			}
		}
		//IF first_arg is Constant and second_arg is variable
		else if(!isVariable(arg1) && isVariable(arg2))
		{
			//check if variable (arg2) already has any assignment in map substitutionMap:theta
			substitutionMapItr it = theta.find(arg2);
			if(it != theta.end())//exisiting substitution found
			{
				//if the existing substitution is same as arg1(Fact)....No issues, hence proceed with next set of args
				if(it->second == arg1)
				{
					continue;//process the next set of corresponding args
				}
				else
				{
					//conflicting Facts for the same variable, cant unify
					cout << " is : FAIL (conflicting Facts for the same variable)" << endl;
					return false;
				}
			}
			else// no exisiting substitution for variable arg1, so add new substitution
			{
				theta[arg2] = arg1;
				continue;//process the next set of corresponding args
			}
		}
		//BOTH ARGS are variables
		else
		{
			cout << "arg2 : " << arg2 << " arg1 : " << arg1 << endl;
			//cout << " is : FAIL (BOTH ARGS are variables!!!!!!!!!!!!!FIGURE OUT HOW TO HANDLE)" << endl;
			//return false;
			
			//check if variable (arg2) already has any assignment in map substitutionMap:theta
			substitutionMapItr it = theta.find(arg2);
			if(it != theta.end())//exisiting substitution found
			{
				//if the existing substitution is same as arg2(variable)....No issues, hence proceed with next set of args
				if(it->second == arg1)
				{
					//Knows(x,y,x), Knows(x1,y,x1)
					continue;//process the next set of corresponding args
				}
				else
				{
					//Knows(x,y,x), Knows(x1,y,x2)
					//conflicting Facts for the same variable, cant unify
					cout << " is : FAIL (conflicting variables for the same variable)" << endl;
					return false;
				}
			}
			else// no exisiting substitution for variable arg1, so add new substitution
			{
				//Knows(x,y), Knows(x1,y1)
				theta[arg2] = arg1;
				continue;//process the next set of corresponding args
			}
		}
	}
	cout << " is : PASS (with subst)";
	//cout << "******************************" << endl;
	//cout << "Variable\tSubstituion" << endl;
	//cout << "==============================" << endl;
	cout << " theta = { ";
	for(substitutionMapItr itr = theta.begin(); itr != theta.end(); ++itr)
	{
		cout << itr->first << "/" << itr->second << "  ";
	}
	cout << "}" << endl;
	//cout << "******************************" << endl;
	return true;
}

void FETCH_RULES_FOR_GOAL(predicate& goal,ruleList& rules);
bool FOL_BC_OR(predicate goal,substitutionMap& theta);
bool FOL_BC_AND(predicateList premise_goals,substitutionMap& theta);

int main(int argc, char *argv[])
{
	//g++ inference.cpp –o inference.o
	//./inference.o –i inputFile
	
	ofstream ofs("output.txt", ios::out | ios::trunc);
	if(!ofs.is_open())
	{
		cout << "Cannot open output file stream" << endl;
		return -1;
	}
	if( argc != 3)
	{
		cout << "Invalid input format. Usage : ./inference.o -i inputFile" << endl;
		return 0;
	}
	if ( strncmp(argv[1],"-i",sizeof("-i")) != 0)
	{
		cout << "Invalid option" << argv[1] << " . Usage : ./inference.o -i inputFile" << endl;
		return 0;
	}
	
	ifstream ifs(argv[2]);
	string line;
	
	////////////////////////////NO OF QUERIES////////////////////////////////////
	int noOfQuery = 0;
	getline(ifs, line);
	noOfQuery = atoi(line.c_str());
	cout << "No of Queries : " << noOfQuery << endl;
	////////////////////////////QUERIES////////////////////////////////////
	predicateList queryList;
	for(int i=0; i<noOfQuery; ++i)
	{
		getline(ifs, line);
		//cout << "DEBUG Parse Query : " << line << endl;
		predicate* query = parsePredicate(line);
		queryList.push_back(*query);
	}
	////////////////////////////NO OF CLAUSES////////////////////////////////////
	int noOfClauses = 0;
	getline(ifs, line);
	noOfClauses = atoi(line.c_str());
	cout << "No of Clauses : " << noOfClauses << endl;
	////////////////////////////CLAUSES////////////////////////////////////
	for(int i=0; i<noOfClauses; ++i)
	{
		getline(ifs, line);
		//cout << "DEBUG Parse Clause : " << line << endl;
		size_t impPos =line.find(" => ");
		if(impPos != string::npos)
		{
			//cout << "DEBUG Horn Clause " ;
			rule* r = parseRule(line,impPos);
			string key = (r->getConclusion())->getName();
			kb_itr it = KB.find(key);
			if(it==KB.end())//Conclusion Key Doesnt exists
			{
				ruleList rules;
				rules.push_back(*r);
				KB[key] = rules;
			}
			else//Conclusion Key exists
			{
				ruleList& rules = it->second;
				rules.push_back(*r);
			}
		}
		else
		{
			//cout << "DEBUG Fact" << endl;
			rule* r = parsePredicateAsRule(line);
			string key = (r->getConclusion())->getName();
			kb_itr it = KB.find(key);
			if(it==KB.end())//Conclusion Key Doesnt exists
			{
				ruleList rules;
				rules.push_back(*r);
				KB[key] = rules;
			}
			else//Conclusion Key exists
			{
				ruleList& rules = it->second;
				rules.push_back(*r);
			}
		}
		//DEBUG cout << endl;
	}
	
	//displayKB();
	//cout << endl << endl;
	orderRulesKB();
	displayOrderedKB();

	string falseStr = "FALSE", trueStr = "TRUE";
	cout << "No of Queries : " << queryList.size() << endl;
	int i = 0;
	for (predicateListItr queryItr = queryList.begin(); queryItr != queryList.end(); queryItr++)
	{
		cout << endl;
		cout << "********************************************" << endl;
		cout << "clearing historyOfGoals" << endl;
		//historyOfGoals.clear();
		newHistoryOfGoals.clear();
		cout << "\n\n\nHandling query : " << ++i << " "; queryItr->display(); cout << endl;
		//search query_predicate_name in orderedKB
		string key = queryItr->getName();
		kb_itr it = orderedKB.find(key);
		if(it==orderedKB.end())//query_predicate Key Doesnt exists
		{
			cout << "No predicate exists in KB which has predicate name of given query : "; queryItr->display();
			ofs << falseStr << endl;
		}
		else
		{		
			bool queryProved = false;
			substitutionMap theta;
			queryProved = FOL_BC_OR(*queryItr,theta);
			if(queryProved)
			{
				cout << "Proved Query : "; queryItr->display(); cout << endl;
				ofs << trueStr << endl;
			}
			else
			{
				cout << "Cannot Prove Query : "; queryItr->display(); cout << endl;
				ofs << falseStr << endl;
			}
		}
	}
	return 0;	
}

void FETCH_RULES_FOR_GOAL(predicate& goal,ruleList& rules)
{
	//search goal_predicate_name in orderedKB
	string key = goal.getName();
	kb_itr it = orderedKB.find(key);
	if(it==orderedKB.end())//goal_predicate Key Doesnt exists
	{
		cout << "No rules exists in KB which has predicate name of given goal : "; goal.display(); cout << " as its conclusion" << endl;
		return;
	}
	else
	{
		rules = it->second;
	}
}


bool FOL_BC_OR(predicate goal,substitutionMap& theta)
{
	cout << "######################################################################################" << endl;
	cout << "FOL_BC_OR() : predicate goal = "; goal.display();
	cout << " theta = { ";
	for(substitutionMapItr itr = theta.begin(); itr != theta.end(); ++itr)
	{
		cout << itr->first << "/" << itr->second << "  ";
	}
	cout << "}" << endl;
	
	/*historyOfGoalsItr goalsItr = historyOfGoals.find(goal.getName());
	if(goalsItr == historyOfGoals.end())
	{
		historyOfGoals[goal.getName()] = goal.getArgs();
		cout << "Added : "; goal.display(); cout << " to historyOfGoals" << endl;
	}
	else
	{
		if(goal.getArgs() == historyOfGoals[goal.getName()])
		{
			cout << "loop detected" ;goal.display();cout << endl;
			//return false;
		}
	}*/
		
	ruleList rules;
	FETCH_RULES_FOR_GOAL(goal, rules);
	cout << "Following Rules can be used to prove : "; goal.display(); cout << endl;
	for (ruleListItr rl_Itr = rules.begin(); rl_Itr != rules.end(); rl_Itr++)
	{
		rl_Itr->display();
	}
	
	//try to unify with any conclusion present
	bool foundRuleUnifier = false;
	bool queryProved = false;
	for (ruleListItr rl_Itr = rules.begin(); rl_Itr != rules.end(); rl_Itr++)//try to unify with each conclusion of all (subset)rules,until we can prove using Backward Chaining
	{
		cout << "\nUsing rule : " ; rl_Itr->display();
		predicate* concl = rl_Itr->getConclusion();
		substitutionMap theta1 = theta;
		foundRuleUnifier = unify(goal,*concl,theta1);
		if(foundRuleUnifier)//goal can be unified with conclusion, now try to prove the premise using BC_Algo
		{
			cout << "add goal : "; goal.display(); cout << ",theta1 : {";
			for(substitutionMapItr itr = theta1.begin(); itr != theta1.end(); ++itr)
			{
				cout << itr->first << "/" << itr->second << "  ";
			}
			cout << "} to historyOfGoals" << endl;
			//forming key
			list<string> goal_name_arg;
			goal_name_arg.push_back(goal.getName());
			list<string>& args = goal.getArgs();
			for(listStringsItr it = args.begin(); it != args.end(); ++it)
			{
				goal_name_arg.push_back(*it);
			}
			/*cout << "key : ";
			for(listStringsItr it = goal_name_arg.begin(); it != goal_name_arg.end(); ++it)
			{
				cout << *it << " , ";
			}
			cout << endl;*/
			//fetch list<substitutionMap>
			newHistoryOfGoalsItr history_Itr = newHistoryOfGoals.find(goal_name_arg);
			if(history_Itr == newHistoryOfGoals.end())//if no list yet add new one
			{
				list<substitutionMap> list_of_substitutionMap;
				list_of_substitutionMap.push_back(theta1);
				newHistoryOfGoals[goal_name_arg] = list_of_substitutionMap;
				//cout << "added key : " << endl;
			}
			else
			{
				//else iterate over existing list to see if substitutionMap is already present
				list<substitutionMap>& exisiting_list_of_substitutionMap = history_Itr->second;
				cout << "key already exists with no of substitutionMaps : " << exisiting_list_of_substitutionMap.size() << endl;
				cout << "try to find theta1 : {";
				for(substitutionMapItr itr = theta1.begin(); itr != theta1.end(); ++itr)
				{
					cout << itr->first << "/" << itr->second << "  ";
				}
				cout << "} in the following : " << endl;
				
				bool found = false;
				for(list<substitutionMap>::iterator subItr = exisiting_list_of_substitutionMap.begin(); subItr != exisiting_list_of_substitutionMap.end(); ++subItr)
				{
					cout << "subItr : {";
					for(substitutionMapItr itr = subItr->begin(); itr != subItr->end(); ++itr)
					{
						cout << itr->first << "/" << itr->second << "  ";
					}
					cout << "}" << endl;
					if(map_compare(*subItr, theta1))
					{
						found = true;
						break;
					}
				}
				if(found)//theta1 substitutionMap is already present in history
				{
					cout << "new loop detected" << endl;
					return false;
				}
				else
				{
					exisiting_list_of_substitutionMap.push_back(theta1);
					cout << "added theta1 as well no of substitutionMaps : " << exisiting_list_of_substitutionMap.size() << endl;
					for(list<substitutionMap>::iterator subItr = exisiting_list_of_substitutionMap.begin(); subItr != exisiting_list_of_substitutionMap.end(); ++subItr)
					{
						cout << "subItr : {";
						for(substitutionMapItr itr = subItr->begin(); itr != subItr->end(); ++itr)
						{
							cout << itr->first << "/" << itr->second << "  ";
						}
						cout << "}" << endl;
					}
				}
			}	
			
			
			
			
			
			cout << "goal successfully unified with conclusion of rule : "; rl_Itr->display();
			//if all premise proven, return true, break processing any more rules and proceed to next query
			queryProved = FOL_BC_AND(*(rl_Itr->getPremises()), theta1);
			if(queryProved)
			{
				//update theta
				theta = theta1;
				return true;
			}
		}
	}
	return false;
}


void SubSt(predicate& org_predicate,substitutionMap& theta,predicate& theta_predicate)
{
	
	theta_predicate.setName(org_predicate.getName());
	
	list<string>& org_args 	 = org_predicate.getArgs();
	list<string>& theta_args = theta_predicate.getArgs();

	for(listStringsItr org_args_itr = org_args.begin(); org_args_itr!=org_args.end() ; ++org_args_itr)
	{
		string arg = *org_args_itr;
		if(isVariable(arg))
		{
			//check if the variable has substitution in substitutionMap
			string key = arg;
			substitutionMapItr it = theta.find(key);
			if(it != theta.end())//if found replace variable with value in predicate arg
			{
				string value = it->second;
				theta_args.push_back(value);
			}
			else
				theta_args.push_back(arg);
		}
		else
		{
			theta_args.push_back(arg);
		}
	}
	
	//cout << "\nIn SubSt : " << endl;
	//cout << "org_predicate : "; org_predicate.display(); cout << endl;
	//cout << "After Substitution : ";
	//cout << " theta = { ";
	//for(substitutionMapItr itr = theta.begin(); itr != theta.end(); ++itr)
	//{
	//	cout << itr->first << "/" << itr->second << "  ";
	//}
	//cout << "}" << endl;
	//cout << "theta_predicate : "; theta_predicate.display(); cout << endl;cout << endl;
}

bool FOL_BC_AND(predicateList premise_goals,substitutionMap& theta)
{
	if(premise_goals.size() == 0)
		return true;
	else
	{
		cout << "######################################################################################" << endl;
		cout << "FOL_BC_AND() : ";
		cout << "predicateList premise_goals = ";
		for(predicateListItr it = premise_goals.begin(); it != premise_goals.end(); ++it)
		{
			it->display(); cout << " ";
		}
		//cout << endl;
		cout << " theta = { ";
		for(substitutionMapItr itr = theta.begin(); itr != theta.end(); ++itr)
		{
			cout << itr->first << "/" << itr->second << "  ";
		}
		cout << "}" << endl;
		
		
		predicate first_premise_goal = premise_goals.front();		premise_goals.pop_front();
		predicateList& rest_premise_goals = premise_goals;
		
		predicate first_premise_goal_subST_theta;
		SubSt(first_premise_goal ,theta, first_premise_goal_subST_theta);
				
		ruleList rules;
		FETCH_RULES_FOR_GOAL(first_premise_goal_subST_theta, rules);
		cout << "Following Rules can be used to prove : "; first_premise_goal_subST_theta.display(); cout << endl;
		for (ruleListItr rl_Itr = rules.begin(); rl_Itr != rules.end(); rl_Itr++)
		{
			rl_Itr->display();
		}
		bool foundRuleUnifier = false;
		bool queryProved = false;
		for (ruleListItr rl_Itr = rules.begin(); rl_Itr != rules.end(); rl_Itr++)//try to unify with each conclusion of all (subset)rules,until we can prove using Backward Chaining
		{
			cout << "\nUsing rule : " ; rl_Itr->display();
			predicate* concl = rl_Itr->getConclusion();
			substitutionMap theta1 = theta;
			foundRuleUnifier = tryUnify(first_premise_goal_subST_theta,*concl,theta1);
			if(foundRuleUnifier)//goal can be unified with conclusion, now try to prove the premise using BC_Algo
			{
				//if all premise proven, return true, break processing any more rules and proceed to next query
				predicate first_premise_goal_subST_theta1;
				SubSt(first_premise_goal_subST_theta ,theta1, first_premise_goal_subST_theta1);
				queryProved = FOL_BC_OR(first_premise_goal_subST_theta1,theta1);
				if(queryProved)
				{
					//cout << "rest_premise_goals : " << rest_premise_goals.size() << endl;
					bool remProved = FOL_BC_AND(rest_premise_goals,theta1);
					if(remProved)
					{
						theta = theta1;
						return true;
					}
				}
			}
		}
		return false;
	}
}
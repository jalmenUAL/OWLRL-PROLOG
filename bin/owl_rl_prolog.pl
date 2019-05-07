%%%%%%%%%%%%%%%%%%
% OWL-RL Prolog implementation
% Jesus Almendros, December, 2011
%%%%%%%%%%%%%%%%%%%

:-module(owl_rl).

:-use_module(library('semweb/rdf_db')).
:-use_module(library('semweb/rdfs')).

 
        
dynamic_pred:-
      dynamic trp_store/3,triple/3,end/0,analysed/3.

%%%%%%%%%%%%%%%%%%%%%%

gen_id([],'').
gen_id([literal(X)|L],Id):-!,gen_id(L,Id2),atom_concat(X,Id2,Id).
gen_id([X|L],Id):-rdf_split_url(_,N,X),gen_id(L,Id2),atom_concat(N,Id2,Id).

%%%%%%%%%%%%%%%%%%%%%%

rdf_db:ns(rdf,  'http://www.w3.org/1999/02/22-rdf-syntax-ns#').
rdf_db:ns(rdfs,  'http://www.w3.org/2000/01/rdf-schema#').
rdf_db:ns(owl,  'http://www.w3.org/2002/07/owl#').
rdf_db:ns(ex, 'http://www.semanticweb.org/ontologies/2011/7/socialnetwork.owl#').
rdf_db:ns(inc, 'http://www.semanticweb.org/inconsistency.owl#').
rdf_db:ns(ax, 'http://www.semanticweb.org/axioms.owl#').

%%%%%%%%%%
%EXPLANATION
%%%%%%%%%%

explanation(_,_,_,_,_):-retractall(analysed(_,_,_)),fail.

explanation(_,_,_,_,_):-rdf_reset_db,fail.

explanation(_,_,_,_,File):-rdf_load(File),fail.

explanation(_,_,_,_,_):-bottom_up_init_explanation,fail.

explanation(_,_,_,_,File):-load_owl(File),fail.

 
explanation(A,B,C,L,_):-  explanation_main(A,B,C,[],L),
				L\=[].

explanation_main(A,B,C,L,[rdf(RA,GOB,RC)|L]):- 
				rdf_global_term(A,GA),rdf_global_term(B,GB),rdf_global_term(C,GC),
				rdf(GA,GB,GC), 
				rdf_global_object(GOA,GA),rdf_global_object(GOB,GB),rdf_global_object(GOC,GC),
				represent(GOA,RA),represent(GOC,RC).
		
explanation_main(A,B,C,L1,L2):-
			rdf_global_term(A,GA),rdf_global_term(B,GB),rdf_global_term(C,GC),
			rdf(GA,GB,GC),
			\+analysed(GA,GB,GC),
			assert(analysed(GA,GB,GC)),
			clause(triple(GA,B,GC),Cond),  
			explanation_condition(Cond,[],LC),
			append(L1,LC,L2).
			
explanation_condition(true,L,L):-!. 

explanation_condition(C,L,L2):-C=..[','|Conditions],!,explanation_list(Conditions,L,L2).
				
explanation_condition(C,L,L2):-C=triple(X,Y,Z),!,	
						 
						explanation_main(X,Y,Z,L,L2).
						 
explanation_condition(C,L,L):-C=gen_id(_,_),!.

explanation_condition(C,L,L):-call(C).

explanation_list([],L,L).

explanation_list([C|RC],L,L2):-explanation_condition(C,L,L1),explanation_list(RC,L1,L2).


bottom_up_init_explanation:-retractall(trp_store_explanation(_,_,_)),fail.

bottom_up_init_explanation:-rdf(X,GY,Z),rdf_global_term(Y,GY),assert(trp_store_explanation(X,Y,Z)),fail.

bottom_up_init_explanation:-rdf_reset_db,fail.

bottom_up_init_explanation.
   

%%%%%%%%%%%%%%%%%%%%
% ALL_EXPLANATIONS
%%%%%%%%%%%%%%%%%%%%

all_explanations(X,Y,Z,Set,File):-findall(L,explanation(X,Y,Z,L,File),List),flatten(List,Flat),list_to_set(Flat,Set).


%%%%%%%%%%%%%%%%%%%
% ROOT EXPLANATIONS
%%%%%%%%%%%%%%%%%%%%


root_explanation(_,_,_,_,_):-retractall(analysed(_,_,_)),fail.

root_explanation(_,_,_,_,_):-rdf_reset_db,fail.

root_explanation(_,_,_,_,File):-rdf_load(File),fail.

root_explanation(_,_,_,_,_):-root_bottom_up_init_explanation,fail.

root_explanation(_,_,_,_,File):-load_owl(File),fail.

 
root_explanation(A,B,C,L,_):-  root_explanation_main(A,B,C,[],L),
				L\=[].

root_explanation_main(A,B,C,L,[rdf(RA,GOB,RC)|L]):- 
				rdf_global_term(A,GA),rdf_global_term(B,GB),rdf_global_term(C,GC),
				rdf(GA,GB,GC),trp_store_explanation(GA,GB,GC),
				rdf_global_object(GOA,GA),rdf_global_object(GOB,GB),rdf_global_object(GOC,GC),
				represent(GOA,RA),represent(GOC,RC).

root_explanation_main(A,B,C,L,L):- 
				rdf_global_term(A,GA),rdf_global_term(B,GB),rdf_global_term(C,GC),
				rdf(GA,GB,GC),\+trp_store_explanation(GA,GB,GC).
			
root_explanation_main(A,B,C,L1,L2):-
			rdf_global_term(A,GA),rdf_global_term(B,GB),rdf_global_term(C,GC),
			rdf(GA,GB,GC),
			\+analysed(GA,GB,GC),
			assert(analysed(GA,GB,GC)),
			clause(triple(GA,B,GC),Cond),  
			root_explanation_condition(Cond,[],LC),
			append(L1,LC,L2).
			
root_explanation_condition(true,L,L):-!. 

root_explanation_condition(C,L,L2):-C=..[','|Conditions],!,root_explanation_list(Conditions,L,L2).
				
root_explanation_condition(C,L,L2):-C=triple(X,Y,Z),!,	
						 
						root_explanation_main(X,Y,Z,L,L2).
						 
root_explanation_condition(C,L,L):-C=gen_id(_,_),!.

root_explanation_condition(C,L,L):-call(C).


root_explanation_list([],L,L).

root_explanation_list([C|RC],L,L2):-root_explanation_condition(C,L,L1),root_explanation_list(RC,L1,L2).


root_bottom_up_init_explanation:-retractall(trp_store_explanation(_,_,_)),fail.

root_bottom_up_init_explanation:-rdf(X,GY,Z),rdf_global_term(Y,GY),assert(trp_store_explanation(X,Y,Z)),fail.

root_bottom_up_init_explanation:-rdf_reset_db,fail.

root_bottom_up_init_explanation.

%%%%%%%%%%%%%%%%%%%%
% ALL_ROOT_EXPLANATIONS
%%%%%%%%%%%%%%%%%%%%

all_root_explanations(X,Y,Z,Set,File):-findall(L,root_explanation(X,Y,Z,L,File),List),flatten(List,Flat),list_to_set(Flat,Set).

 
%%%%%%%%%%%%%%%%%%%
% LEMMA EXPLANATIONS
%%%%%%%%%%%%%%%%%%%%


lemma_explanation(_,_,_,_,_):-retractall(analysed(_,_,_)),fail.

lemma_explanation(_,_,_,_,_):-rdf_reset_db,fail.

lemma_explanation(_,_,_,_,File):-rdf_load(File),fail.

lemma_explanation(_,_,_,_,_):-root_bottom_up_init_explanation,fail.

lemma_explanation(_,_,_,_,File):-load_owl(File),fail.

 
lemma_explanation(A,B,C,L,_):-  lemma_explanation_main(A,B,C,[],L),
				L\=[].

lemma_explanation_main(A,B,C,L,[rdf(RA,GOB,RC)|L]):- 
				rdf_global_term(A,GA),rdf_global_term(B,GB),rdf_global_term(C,GC),
				rdf(GA,GB,GC),\+trp_store_explanation(GA,GB,GC),
				rdf_global_object(GOA,GA),rdf_global_object(GOB,GB),rdf_global_object(GOC,GC),
				represent(GOA,RA),represent(GOC,RC).

lemma_explanation_main(A,B,C,L,L):- 
				rdf_global_term(A,GA),rdf_global_term(B,GB),rdf_global_term(C,GC),
				rdf(GA,GB,GC),trp_store_explanation(GA,GB,GC).
			
lemma_explanation_main(A,B,C,L1,L2):-
			rdf_global_term(A,GA),rdf_global_term(B,GB),rdf_global_term(C,GC),
			rdf(GA,GB,GC),
			\+analysed(GA,GB,GC),
			assert(analysed(GA,GB,GC)),
			clause(triple(GA,B,GC),Cond),  
			lemma_explanation_condition(Cond,[],LC),
			append(L1,LC,L2).
			
lemma_explanation_condition(true,L,L):-!. 

lemma_explanation_condition(C,L,L2):-C=..[','|Conditions],!,lemma_explanation_list(Conditions,L,L2).
				
lemma_explanation_condition(C,L,L2):-C=triple(X,Y,Z),!,	
						 
						lemma_explanation_main(X,Y,Z,L,L2).
						 
lemma_explanation_condition(C,L,L):-C=gen_id(_,_),!.

lemma_explanation_condition(C,L,L):-call(C).


lemma_explanation_list([],L,L).

lemma_explanation_list([C|RC],L,L2):-lemma_explanation_condition(C,L,L1),lemma_explanation_list(RC,L1,L2).


lemma_bottom_up_init_explanation:-retractall(trp_store_explanation(_,_,_)),fail.

lemma_bottom_up_init_explanation:-rdf(X,GY,Z),rdf_global_term(Y,GY),assert(trp_store_explanation(X,Y,Z)),fail.

lemma_bottom_up_init_explanation:-rdf_reset_db,fail.

lemma_bottom_up_init_explanation.

%%%%%%%%%%%%%%%%%%%%
% ALL_LEMMA_EXPLANATIONS
%%%%%%%%%%%%%%%%%%%%

all_lemma_explanations(X,Y,Z,Set,File):-findall(L,lemma_explanation(X,Y,Z,L,File),List),flatten(List,Flat),list_to_set(Flat,Set).

%%%%%%%%%%%%%%%%%%%%
% JUSTIFICATION
%%%%%%%%%%%%%%%%%%%%

justification(X,Y,Z,J,File):-all_justifications(X,Y,Z,Set,File),member(J,Set).

all_justifications(X,Y,Z,Set,File):-findall(L,explanation(X,Y,Z,L,File),List),minimal_list(List,[],Set).

minimal_list([],L,L).

minimal_list([X|L1],Sol,L2):-member(Y,Sol),subset(Y,X),!,minimal_list(L1,Sol,L2).

minimal_list([X|L1],Sol,L2):-append(Sol,[X],New),minimal_list(L1,New,L2).
 
%%%%%%%%%%%%%%%%%%%%
% ROOT JUSTIFICATION
%%%%%%%%%%%%%%%%%%%%

root_justification(X,Y,Z,J,File):-all_root_justifications(X,Y,Z,Set,File),member(J,Set).

all_root_justifications(X,Y,Z,Set,File):-findall(L,root_explanation(X,Y,Z,L,File),List),minimal_list(List,[],Set).

%%%%%%%%%%%%%%%%%%%%
% LEMMA JUSTIFICATION
%%%%%%%%%%%%%%%%%%%%

lemma_justification(X,Y,Z,J,File):-all_lemma_justifications(X,Y,Z,Set,File),member(J,Set).

all_lemma_justifications(X,Y,Z,Set,File):-findall(L,lemma_explanation(X,Y,Z,L,File),List),minimal_list(List,[],Set).


%%%%%%%%%%%%%%%
% write_class
%%%%%%%%%%%%%%%%

write_class(C):-rdf(C,rdf:type,'http://www.w3.org/2002/07/owl#Restriction'),
		      rdf(C,'http://www.w3.org/2002/07/owl#onProperty',P),
		      rdf(C, 'http://www.w3.org/2002/07/owl#hasValue',V),!,
		      write('Class Restriction:'),nl,write('Property:'),nl,write(P),nl,write('Has Value:'),nl,write(V),nl.

write_class(C):-rdf(C,rdf:type,'http://www.w3.org/2002/07/owl#Restriction'),
		      rdf(C,'http://www.w3.org/2002/07/owl#onProperty',P),
		      rdf(C, 'http://www.w3.org/2002/07/owl#allValuesFrom',V),!,
		      write('Class Restriction:'),nl,write('Property:'),nl,write(P),nl,write('All Values From:'),nl,write(V),nl.
 
write_class(C):-rdf(C,rdf:type,'http://www.w3.org/2002/07/owl#Restriction'),
		      rdf(C,'http://www.w3.org/2002/07/owl#onProperty',P),
		      rdf(C, 'http://www.w3.org/2002/07/owl#someValuesFrom',V),!,
		      write('Class Restriction:'),nl,write('Property:'),nl,write(P),nl,write('Some Values From:'),nl,write(V),nl.
 
write_class(C):-write('Class:'),nl,write(C).
 
 
represent(C,exists(GP,GV)):-rdf_global_term(C,GC),rdf(GC,rdf:type,'http://www.w3.org/2002/07/owl#Restriction'),
		      rdf(GC,'http://www.w3.org/2002/07/owl#onProperty',P),
		      rdf_global_object(GP,P),
		      rdf(GC, 'http://www.w3.org/2002/07/owl#hasValue',V),
		      rdf_global_object(GV,V),!.

represent(C,all(GP,GV)):-rdf_global_term(C,GC),rdf(GC,rdf:type,'http://www.w3.org/2002/07/owl#Restriction'),
		      rdf(GC,'http://www.w3.org/2002/07/owl#onProperty',P),
		      rdf_global_object(GP,P),
		      rdf(GC, 'http://www.w3.org/2002/07/owl#allValuesFrom',V),
		      rdf_global_object(GV,V),!.
 
represent(C,exists(GP,GV)):-rdf_global_term(C,GC),rdf(GC,rdf:type,'http://www.w3.org/2002/07/owl#Restriction'),
		      rdf(GC,'http://www.w3.org/2002/07/owl#onProperty',P),
		      rdf_global_object(GP,P),
		      rdf(GC, 'http://www.w3.org/2002/07/owl#someValuesFrom',V),
		      rdf_global_object(GV,V),!.
 
represent(C,C).
 
%%%%%%%%%%%%%%%%%%%%%%%%
% LOAD
%%%%%%%%%%%%%%%%%%%%%%%

load_owl(File):-
		rdf_reset_db,
		rdf_load(File),
		bottom_up_main,
		ontology_inconsistency.
		
		
ontology_inconsistency:- rdf(_,rdf:type,'http://www.semanticweb.org/inconsistency.owl#Inconsistency'),!,
						write('ONTOLOGY SEEMS TO BE NOT CONSISTENT'),nl.
ontology_inconsistency:- rdf(_,rdf:type,'http://www.semanticweb.org/inconsistency.owl#Warning'),!,
						write('THERE ARE SOME WARNINGS'),nl.		
ontology_inconsistency:- write('ONTOLOGY IS CONSISTENT'),nl.		
		 
 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% BOTTOM-UP-MAIN
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

bottom_up_main:-bottom_up_procedure,fail.

bottom_up_main.  

%%%%%%%%%
% BOTTOM-UP-PROCEDURE
%%%%%%%%%%%

bottom_up_procedure:-bottom_up_init,fail.

bottom_up_procedure:-assert(end),bottom_up_step.

bottom_up_procedure.

bottom_up_step:-clean,update,bottom_up_rule,(end->bottom_up_step;fail).

bottom_up_step.

%%%%%%%%%
% UPDATE
%%%%%%%%%%%
 
 
 
update:-trp_store(X,Y,Z),X\=literal(_),rdf_global_term(Y,GY),rdf_assert(X,GY,Z),fail.

update:-retractall(trp_store(_,_,_)),fail.

update.

%%%%%%%%%
% CLEAN
%%%%%%%%%%%

clean:-retractall(end),fail.

clean.

%%%%%%%%%
% BOTTOM-UP-INIT
%%%%%%%%%%%


bottom_up_init:-retractall(trp_store(_,_,_)),fail.

bottom_up_init:-rdf(X,GY,Z),rdf_global_term(Y,GY),assert(trp_store(X,Y,Z)),fail.

bottom_up_init:-rdf_reset_db,fail.

bottom_up_init.


%%%%%%%%%
% BOTTOM-UP-RULE
%%%%%%%%%%%

 

bottom_up_rule:-clause(triple(X,Y,Z),C),
				call_condition(C),rdf_global_term(Y,GY), 
				(rdf(X,GY,Z)->fail;
				(\+end,X\=literal(_)->assert(end);true),
				(X\=literal(_)->assert(trp_store(X,Y,Z));true),fail).
bottom_up_rule.

 
%%%%%%%%%%%%%%%%%%%%%%%%%%
% CALL_CONDITION
%%%%%%%%%%%%%%%%%%%%%%%%%%%

call_condition(true):-!. 

call_condition(C):-C=..[','|Conditions],!,call_list(Conditions).

call_condition(C):-C=triple(X,Y,Z),!,rdf_global_term(Y,GY),rdf(X,GY,Z).

call_condition(C):-call(C).

call_list([]).

call_list([C|RC]):-call_condition(C),call_list(RC).

%%%%%%%%%
% TYPE-LIST
%%%%%%%%%%%

type_list(_,[]).

type_list(Y,[C|RC]):- rdf(Y,rdf:type,C),type_list(Y,RC). 

%%%%%%%%%
% TYPE-COLLECTION
%%%%%%%%%%%
 
type_collection(Y,Collection):-rdfs_list_to_prolog_list(Collection,List),type_list(Y,List).
 
 
%%%%%%%%%
% PROPERTYCHAINAXIOM-LIST
%%%%%%%%%%% 
 
propertyChainAxiom_list(_,X,[P],V):-rdf(X,P,V).

propertyChainAxiom_list(U,X,[P|RP],V):-rdf(X,P,Z),propertyChainAxiom_list(U,Z,RP,V). 
 
%%%%%%%%%
% PROPERTYCHAINAXIOM-COLLECTION
%%%%%%%%%%%  
 
propertyChainAxiom_collection(U,Collection,V):-rdfs_list_to_prolog_list(Collection,List),propertyChainAxiom_list(U,U,List,V).
 
 

 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% OWL RL
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%
% eq-ref	 
%%%%%%%%

%triple(S, owl:sameAs, S) :- triple(S, _, _).

%triple(GP, owl:sameAs, GP) :- triple(_, P, _),rdf_global_term(P,GP).

%triple(O, owl:sameAs, O) :- triple(_, _, O).

%%%%%%%
%eq-sym	
%%%%%%%%

triple(Y, owl:sameAs, X) :- triple(X, owl:sameAs, Y).	 

%%%%
% eq-trans	
%%%%%

triple(X, owl:sameAs, Z):-triple(X, owl:sameAs, Y),triple(Y, owl:sameAs, Z).

%%%%%%
%eq-rep-s	
%%%%%%%

 
triple(SS, P, O) :- triple(S, owl:sameAs, SS),
			triple(S, P, O),
			rdf_global_term(P,GP),
			rdf_split_url(D,_,GP),
			D\='http://www.semanticweb.org/inconsistency.owl#'.

%%%%
%eq-rep-p	
%%%%%

 
triple(S, PP, O):-triple(P, owl:sameAs, PP),
			triple(S, P, O),
			rdf_global_term(P,GP),
			rdf_split_url(D,_,GP),
			D\='http://www.semanticweb.org/inconsistency.owl#'.


%%%%%%%%
%eq-rep-o
%%%%%%%%

 
triple(S, P, OO):-triple(O, owl:sameAs, OO), 
			triple(S, P, O),
			rdf_global_term(P,GP),
			rdf_split_url(D,_,GP),
			D\='http://www.semanticweb.org/inconsistency.owl#'.


%%%%%%%%
%eq-diff1
%%%%%%%%

triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#Inconsistency'):-
					triple(X, owl:sameAs, Y),
					triple(X, owl:differentFrom, Y),
					gen_id(['error_ ',X,' is the same as and different from ',Y],Id).

 
triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#SameAndDifferentIndividuals'):-
					triple(X, owl:sameAs, Y),
					triple(X, owl:differentFrom, Y),
					gen_id(['error_ ',X,' is the same as and different from ',Y],Id).
triple(Id,inc:individual,X):-
					triple(X, owl:sameAs, Y),
					triple(X, owl:differentFrom, Y),
					gen_id(['error_ ',X,' is the same as and different from ',Y],Id).

triple(Id,inc:individual,Y):-
					triple(X, owl:sameAs, Y),
					triple(X, owl:differentFrom, Y),
					gen_id(['error_ ',X,' is the same as and different from ',Y],Id).					 
%%%%%%%%
%eq-diff2
%%%%%%%%



triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#Inconsistency') :- 
					triple(X, rdf:type,  'http://www.w3.org/2002/07/owl#AllDifferent'), 
					triple(X, owl:members, Y),
					rdfs_member(Z1,Y),
					rdfs_member(Z2,Y),
					Z1\=Z2,
					triple(Z1, owl:sameAs, Z2),
					gen_id(['error_ ',Z1,' is the same as and different from ',Z2],Id).
					
triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#SameAndDifferentIndividuals'):-
					triple(X, rdf:type,  'http://www.w3.org/2002/07/owl#AllDifferent'), 
					triple(X, owl:members, Y),
					rdfs_member(Z1,Y),
					rdfs_member(Z2,Y),
					Z1\=Z2,
					triple(Z1, owl:sameAs, Z2),
					gen_id(['error_ ',Z1,' is the same as and different from ',Z2],Id).

triple(Id,inc:individual,Z1):-
					triple(X, rdf:type,  'http://www.w3.org/2002/07/owl#AllDifferent'), 
					triple(X, owl:members, Y),
					rdfs_member(Z1,Y),
					rdfs_member(Z2,Y),
					Z1\=Z2,
					triple(Z1, owl:sameAs, Z2),
					gen_id(['error_ ',Z1,' is the same as and different from ',Z2],Id).

triple(Id,inc:individual,Z2):-
					triple(X, rdf:type,  'http://www.w3.org/2002/07/owl#AllDifferent'), 
					triple(X, owl:members, Y),
					rdfs_member(Z1,Y),
					rdfs_member(Z2,Y),
					Z1\=Z2,
					triple(Z1, owl:sameAs, Z2),
					gen_id(['error_ ',Z1,' is the same as and different from ',Z2],Id).
%%%%%%%%%
%eq-diff3
%%%%%%%%

triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#Inconsistency'):- 
					triple(X, rdf:type,  'http://www.w3.org/2002/07/owl#AllDifferent'),
					triple(X, owl:distinctMembers, Y),
					rdfs_member(Z1,Y),
					rdfs_member(Z2,Y),
					Z1\=Z2,
					triple(Z1,owl:sameAs, Z2),
					gen_id(['error_ ',Z1,' is the same as and different from ',Z2],Id).

triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#SameAndDifferentIndividuals'):-		
					triple(X, rdf:type,  'http://www.w3.org/2002/07/owl#AllDifferent'),
					triple(X, owl:distinctMembers, Y),
					rdfs_member(Z1,Y),
					rdfs_member(Z2,Y),
					Z1\=Z2,
					triple(Z1,owl:sameAs, Z2),
					gen_id(['error_ ',Z1,' is the same as and different from ',Z2],Id).
					
triple(Id,inc:individual,Z1):-		
					triple(X, rdf:type,  'http://www.w3.org/2002/07/owl#AllDifferent'),
					triple(X, owl:distinctMembers, Y),
					rdfs_member(Z1,Y),
					rdfs_member(Z2,Y),
					Z1\=Z2,
					triple(Z1,owl:sameAs, Z2),
					gen_id(['error_ ',Z1,' is the same as and different from ',Z2],Id).

triple(Id,inc:individual,Z2):-		
					triple(X, rdf:type,  'http://www.w3.org/2002/07/owl#AllDifferent'),
					triple(X, owl:distinctMembers, Y),
					rdfs_member(Z1,Y),
					rdfs_member(Z2,Y),
					Z1\=Z2,
					triple(Z1,owl:sameAs, Z2),
					gen_id(['error_ ',Z1,' is the same as and different from ',Z2],Id).
%%%%%%%%%
%prp-ap	
%%%%%%%

%triple(AP, rdf:type,  'http://www.w3.org/2002/07/owl#AnnotationProperty'):-anotation_property(AP).

%%%%%%%
%prp-dom
%%%%%%%

triple(X, rdf:type, C):-triple(P, rdfs:domain, C),triple(X, P, _).	 

%%%%%%%
%prp-rng
%%%%%%%%

triple(Y, rdf:type, C):-triple(P, rdfs:range, C),triple(_, P, Y).	 



%%%%%%
%prp-fp
%%%%%%	 

triple(Y1, owl:sameAs, Y2):- 
					triple(P, rdf:type,  'http://www.w3.org/2002/07/owl#FunctionalProperty'),
					triple(X, P, Y1),
					triple(X, P, Y2),
					Y1\=Y2.
					
triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#Warning'):-
					triple(P, rdf:type,  'http://www.w3.org/2002/07/owl#FunctionalProperty'),
					triple(X, P, Y1),
					triple(X, P, Y2),
					Y1\=Y2,
					gen_id(['warning_ ',X,' has range ',Y1,' and ',Y2,' in ',P],Id).
						 
triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#SameIndividuals'):-
					triple(P, rdf:type,  'http://www.w3.org/2002/07/owl#FunctionalProperty'),
					triple(X, P, Y1),
					triple(X, P, Y2),Y1\=Y2,
					gen_id(['warning_ ',X,' has range ',Y1,' and ',Y2,' in ',P],Id).
					
triple(Id,inc:domain,X):-
					triple(P, rdf:type,  'http://www.w3.org/2002/07/owl#FunctionalProperty'),
					triple(X, P, Y1),
					triple(X, P, Y2),Y1\=Y2,
					gen_id(['warning_ ',X,' has range ',Y1,' and ',Y2,' in ',P],Id).			
					
triple(Id,inc:property,P):-
					triple(P, rdf:type,  'http://www.w3.org/2002/07/owl#FunctionalProperty'),
					triple(X, P, Y1),
					triple(X, P, Y2),Y1\=Y2,
					gen_id(['warning_ ',X,' has range ',Y1,' and ',Y2,' in ',P],Id).
					
triple(Id,inc:range,Y1):-
					triple(P, rdf:type,  'http://www.w3.org/2002/07/owl#FunctionalProperty'),
					triple(X, P, Y1),
					triple(X, P, Y2),Y1\=Y2,
					gen_id(['warning_ ',X,' has range ',Y1,' and ',Y2,' in ',P],Id).

triple(Id,inc:range,Y2):-
					triple(P, rdf:type,  'http://www.w3.org/2002/07/owl#FunctionalProperty'),
					triple(X, P, Y1),
					triple(X, P, Y2),Y1\=Y2,
					gen_id(['warning_ ',X,' has range ',Y1,' and ',Y2,' in ',P],Id).
%%%%%%
%prp-ifp
%%%%%%

triple(X1, owl:sameAs, X2):-triple(P, rdf:type,  'http://www.w3.org/2002/07/owl#InverseFunctionalProperty'),
					triple(X1, P, Y),
					triple(X2, P, Y),
					X1\=X2.

triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#Warning'):-
					triple(P, rdf:type,  'http://www.w3.org/2002/07/owl#InverseFunctionalProperty'),
					triple(X1, P, Y),
					triple(X2, P, Y),
					X1\=X2,
					gen_id(['warning_ ',Y,' has domain ',X1,' and ',X2,' in ',P],Id).

triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#SameIndividuals'):-
					triple(P, rdf:type,  'http://www.w3.org/2002/07/owl#InverseFunctionalProperty'),
					triple(X1, P, Y),
					triple(X2, P, Y),
					X1\=X2,
					gen_id(['warning_ ',Y,' has domain ',X1,' and ',X2,' in ',P],Id).

triple(Id,inc:range,Y):-
					triple(P, rdf:type,  'http://www.w3.org/2002/07/owl#InverseFunctionalProperty'),
					triple(X1, P, Y),
					triple(X2, P, Y),
					X1\=X2,
					gen_id(['warning_ ',Y,' has domain ',X1,' and ',X2,' in ',P],Id).

triple(Id,inc:property,P):-
					triple(P, rdf:type,  'http://www.w3.org/2002/07/owl#InverseFunctionalProperty'),
					triple(X1, P, Y),
					triple(X2, P, Y),
					X1\=X2,
					gen_id(['warning_ ',Y,' has domain ',X1,' and ',X2,' in ',P],Id).
triple(Id,inc:domain,X1):-
					triple(P, rdf:type,  'http://www.w3.org/2002/07/owl#InverseFunctionalProperty'),
					triple(X1, P, Y),
					triple(X2, P, Y),
					X1\=X2,
					gen_id(['warning_ ',Y,' has domain ',X1,' and ',X2,' in ',P],Id).

triple(Id,inc:domain,X2):-
					triple(P, rdf:type,  'http://www.w3.org/2002/07/owl#InverseFunctionalProperty'),
					triple(X1, P, Y),
					triple(X2, P, Y),
					X1\=X2,
					gen_id(['warning_ ',Y,' has domain ',X1,' and ',X2,' in ',P],Id).
					
%%%%%%
%prp-irp
%%%%%%

triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#Inconsistency'):-
				triple(P, rdf:type,  'http://www.w3.org/2002/07/owl#IrreflexiveProperty'),
				triple(X, P, X),
				gen_id(['error_ ',P,' is reflexive in ',X],Id).
				
triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#IrreflexiveProperty'):- 
				triple(P, rdf:type,  'http://www.w3.org/2002/07/owl#IrreflexiveProperty'),
				triple(X, P, X),
				gen_id(['error_ ',P,' is reflexive in ',X],Id).

triple(Id,inc:property,P):- 
				triple(P, rdf:type,  'http://www.w3.org/2002/07/owl#IrreflexiveProperty'),
				triple(X, P, X),
				gen_id(['error_ ',P,' is reflexive in ',X],Id).
				
triple(Id,inc:individual,X):- 
				triple(P, rdf:type,  'http://www.w3.org/2002/07/owl#IrreflexiveProperty'),
				triple(X, P, X),
				gen_id(['error_ ',P,' is reflexive in ',X],Id).

%%%%%%%
%prp-symp
%%%%%%%

triple(Y, P, X):-triple(P, rdf:type,  'http://www.w3.org/2002/07/owl#SymmetricProperty'),
				triple(X, P, Y).	 

%%%%%%%
%prp-asyp
%%%%%%%

triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#Inconsistency'):-
					triple(P, rdf:type,  'http://www.w3.org/2002/07/owl#AsymmetricProperty'),
					triple(X,P,Y),
					triple(Y,P,X),
					gen_id(['error_ ',P,' is symmetric in ',X,' and ',Y],Id).

triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#AsymmetricProperty'):-
					triple(P, rdf:type,  'http://www.w3.org/2002/07/owl#AsymmetricProperty'),
					triple(X,P,Y),
					triple(Y,P,X),
					gen_id(['error_ ',P,' is symmetric in ',X,' and ',Y],Id).
					
triple(Id,inc:property,P):-
					triple(P, rdf:type,  'http://www.w3.org/2002/07/owl#AsymmetricProperty'),
					triple(X,P,Y),
					triple(Y,P,X),
					gen_id(['error_ ',P,' is symmetric in ',X,' and ',Y],Id).

triple(Id,inc:individual,X):-
					triple(P, rdf:type,  'http://www.w3.org/2002/07/owl#AsymmetricProperty'),
					triple(X,P,Y),
					triple(Y,P,X),
					gen_id(['error_ ',P,' is symmetric in ',X,' and ',Y],Id).

triple(Id,inc:individual,Y):-
					triple(P, rdf:type,  'http://www.w3.org/2002/07/owl#AsymmetricProperty'),
					triple(X,P,Y),
					triple(Y,P,X),
					gen_id(['error_ ',P,' is symmetric in ',X,' and ',Y],Id).
					
 
					
%%%%%%%%
%prp-trp
%%%%%%%%

triple(X,P,Z):-triple(P, rdf:type,  'http://www.w3.org/2002/07/owl#TransitiveProperty'),
			triple(X,P,Y),
			triple(Y,P,Z).

%%%%%%%
%prp-spo1	
%%%%%%%

triple(X,P2,Y):-triple(P1, rdfs:subPropertyOf, P2),
			triple(X,P1,Y).

%%%%%%%
%prp-spo2
%%%%%%%%

 

triple(U1, P, Un):-triple(P, owl:propertyChainAxiom,X),
				propertyChainAxiom_collection(U1,X,Un).


%%%%%%%%
%prp-eqp1
%%%%%%%%

triple(X,P2,Y):-triple(P1, owl:equivalentProperty, P2), 
			triple(X,P1,Y).	 

%%%%%%%
%prp-eqp2
%%%%%%%%

triple(X,P1,Y):-triple(P1, owl:equivalentProperty, P2),
			triple(X,P2,Y).	 

%%%%%%
%prp-pdw
%%%%%%

triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#Inconsistency'):-
					triple(P1, owl:propertyDisjointWith, P2),
					triple(X,P1,Y),
					triple(X,P2,Y),
					gen_id(['error_ ',P1,' and ', P2,' hold for ',X,' and ',Y],Id).
			                 
triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#DisjointProperties'):-
					triple(P1, owl:propertyDisjointWith, P2),
					triple(X,P1,Y),
					triple(X,P2,Y),
					gen_id(['error_ ',P1,' and ', P2,' hold for ',X,' and ',Y],Id).
					
triple(Id,inc:property,P1):-
					triple(P1, owl:propertyDisjointWith, P2),
					triple(X,P1,Y),
					triple(X,P2,Y),
					gen_id(['error_ ',P1,' and ', P2,' hold for ',X,' and ',Y],Id).
					
triple(Id,inc:property,P2):-
					triple(P1, owl:propertyDisjointWith, P2),
					triple(X,P1,Y),
					triple(X,P2,Y),
					gen_id(['error_ ',P1,' and ', P2,' hold for ',X,' and ',Y],Id).				             

triple(Id,inc:domain,X):-
					triple(P1, owl:propertyDisjointWith, P2),
					triple(X,P1,Y),
					triple(X,P2,Y),
					gen_id(['error_ ',P1,' and ', P2,' hold for ',X,' and ',Y],Id).
					
triple(Id,inc:range,Y):-
					triple(P1, owl:propertyDisjointWith, P2),
					triple(X,P1,Y),
					triple(X,P2,Y),
					gen_id(['error_ ',P1,' and ', P2,' hold for ',X,' and ',Y],Id).

%%%%%%
%prp-adp
%%%%%%%

triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#Inconsistency'):-
					triple(X, rdf:type,  'http://www.w3.org/2002/07/owl#AllDisjointProperties'),
					triple(X, owl:members, Y),
					rdfs_member(P1,Y),
					rdfs_member(P2,Y),
					P1\=P2, 
					triple(U,P1,V),
					triple(U,P2,V),
					gen_id(['error_ ',P1,' and ', P2,' hold for ',U,' and ',V],Id).
			                 
triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#DisjointProperties'):-
					triple(X, rdf:type,  'http://www.w3.org/2002/07/owl#AllDisjointProperties'),
					triple(X, owl:members, Y),
					rdfs_member(P1,Y),
					rdfs_member(P2,Y), 
					P1\=P2,
					triple(U,P1,V),
					triple(U,P2,V),
					gen_id(['error_ ',P1,' and ', P2,' hold for ',U,' and ',V],Id).


triple(Id,inc:property,P1):-
					triple(X, rdf:type,  'http://www.w3.org/2002/07/owl#AllDisjointProperties'),
					triple(X, owl:members, Y),
					rdfs_member(P1,Y),
					rdfs_member(P2,Y), 
					P1\=P2,
					triple(U,P1,V),
					triple(U,P2,V),
					gen_id(['error_ ',P1,' and ', P2,' hold for ',U,' and ',V],Id).
					
triple(Id,inc:property,P2):-
					triple(X, rdf:type,  'http://www.w3.org/2002/07/owl#AllDisjointProperties'),
					triple(X, owl:members, Y),
					rdfs_member(P1,Y),
					rdfs_member(P2,Y), 
					P1\=P2,
					triple(U,P1,V),
					triple(U,P2,V),
					gen_id(['error_ ',P1,' and ', P2,' hold for ',U,' and ',V],Id).				

triple(Id,inc:domain,U):-
					triple(X, rdf:type,  'http://www.w3.org/2002/07/owl#AllDisjointProperties'),
					triple(X, owl:members, Y),
					rdfs_member(P1,Y),
					rdfs_member(P2,Y), 
					P1\=P2,
					triple(U,P1,V),
					triple(U,P2,V),
					gen_id(['error_ ',P1,' and ', P2,' hold for ',U,' and ',V],Id).	
					
triple(Id,inc:range,V):-
					triple(X, rdf:type,  'http://www.w3.org/2002/07/owl#AllDisjointProperties'),
					triple(X, owl:members, Y),
					rdfs_member(P1,Y),
					rdfs_member(P2,Y), 
					P1\=P2,
					triple(U,P1,V),
					triple(U,P2,V),
					gen_id(['error_ ',P1,' and ', P2,' hold for ',U,' and ',V],Id).	
%%%%%%
%prp-inv1
%%%%%%%

triple(Y,P2,X):-triple(P1, owl:inverseOf, P2),triple(X,P1,Y).	 

%%%%%%
%prp-inv2
%%%%%%%

triple(Y,P1,X):-triple(P1, owl:inverseOf, P2),triple(X,P2,Y).	 

%%%%%%%
%prp-key
%%%%%%%


%triple(?x, owl:sameAs, ?y):-triple(?c, owl:hasKey, ?u),LIST[?u, ?p1, ..., ?pn],triple(?x, rdf:type, ?c),triple(?x, ?p1, ?%z1),...,triple(?x, ?pn, ?zn),triple(?y, rdf:type, ?c),triple(?y, ?p1, ?z1),...,triple(?y, ?pn, ?zn).	 

%%%%%%%
%prp-npa1
%%%%%%%
	 
triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#Inconsistency'):-
					triple(X, owl:sourceIndividual, I1),
					triple(X, owl:assertionProperty, P),
					triple(X, owl:targetIndividual, I2),
					triple(I1,P,I2),
					gen_id(['error_ ',P,' holds for ',I1,' and ',I2],Id).
			                
triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#NegativeAssertionProperty'):-
					triple(X, owl:sourceIndividual, I1),
					triple(X, owl:assertionProperty, P),
					triple(X, owl:targetIndividual, I2),
					triple(I1,P,I2),
					gen_id(['error_ ',P,' holds for ',I1,' and ',I2],Id).
					
triple(Id,inc:property,P):-
					triple(X, owl:sourceIndividual, I1),
					triple(X, owl:assertionProperty, P),
					triple(X, owl:targetIndividual, I2),
					triple(I1,P,I2),
					gen_id(['error_ ',P,' holds for ',I1,' and ',I2],Id).
triple(Id,inc:domain,I1):-
					triple(X, owl:sourceIndividual, I1),
					triple(X, owl:assertionProperty, P),
					triple(X, owl:targetIndividual, I2),
					triple(I1,P,I2),
					gen_id(['error_ ',P,' holds for ',I1,' and ',I2],Id).

triple(Id,inc:range,I2):-
					triple(X, owl:sourceIndividual, I1),
					triple(X, owl:assertionProperty, P),
					triple(X, owl:targetIndividual, I2),
					triple(I1,P,I2),
					gen_id(['error_ ',P,' holds for ',I1,' and ',I2],Id).				
%%%%%
%prp-npa2
%%%%%

triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#Inconsistency'):-
					triple(X, owl:sourceIndividual, I),
					triple(X, owl:assertionProperty, P),
					triple(X, owl:targetValue, LT),
					triple(I,P,LT),
					gen_id(['error_ ',P,' holds for ',I,' and ',LT],Id).
			                 
triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#NegativeAssertionProperty'):-
					triple(X, owl:sourceIndividual, I),
					triple(X, owl:assertionProperty, P),
					triple(X, owl:targetValue, LT),
					triple(I,P,LT),
					gen_id(['error_ ',P,' holds for ',I,' and ',LT],Id).               

triple(Id,inc:property,P):-
					triple(X, owl:sourceIndividual, I),
					triple(X, owl:assertionProperty, P),
					triple(X, owl:targetValue, LT),
					triple(I,P,LT),
					gen_id(['error_ ',P,' holds for ',I,' and ',LT],Id).
					
triple(Id,inc:individual,I):-
					triple(X, owl:sourceIndividual, I),
					triple(X, owl:assertionProperty, P),
					triple(X, owl:targetValue, LT),
					triple(I,P,LT),
					gen_id(['error_ ',P,' holds for ',I,' and ',LT],Id).					
%%%%%%%%%%%%%

%%%%%
% cls-thing	
%%%%

triple('http://www.w3.org/2002/07/owl#Thing', rdf:type,  'http://www.w3.org/2002/07/owl#Class').

%%%%%%%
%cls-nothing1	
%%%%%%

triple('http://www.w3.org/2002/07/owl#Nothing', rdf:type,  'http://www.w3.org/2002/07/owl#Class').

%%%%%%%%
%cls-nothing2
%%%%%%

triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#Inconsistency'):-
				triple(C, rdf:type,  'http://www.w3.org/2002/07/owl#Nothing'),
				gen_id(['error_ empty class ',C],Id).
				
triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#EmptyClass'):-
						triple(C, rdf:type,  'http://www.w3.org/2002/07/owl#Nothing'),
						gen_id(['error_ empty class ',C],Id).
			                 
triple(Id,inc:class,C):-
						triple(C, rdf:type,  'http://www.w3.org/2002/07/owl#Nothing'),
						gen_id(['error_ empty class ',C],Id).
						

%%%%%%
%cls-int1
%%%%%

triple(Y, rdf:type, C):-triple(C, owl:intersectionOf, X),type_collection(Y,X).

%%%%%%
%cls-int2
%%%%%%%

triple(Y, rdf:type, D):-triple(C, owl:intersectionOf, X),
				rdfs_member(D,X),
				triple(Y,rdf:type,C).


%%%%%%
%cls-uni
%%%%%%%

triple(Y, rdf:type, C):-triple(C, owl:unionOf, X),
				rdfs_member(D,X),
				triple(Y, rdf:type,D). 	

%%%%%%
%cls-com
%%%%%%

triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#Inconsistency'):-
					triple(C1, owl:complementOf, C2),
					triple(X, rdf:type, C1),
					triple(X, rdf:type,C2),
					gen_id(['error_ ',X,' belongs to ',C1,' and ',C2],Id).
			                 
triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#DisjointClasses'):-
					triple(C1, owl:complementOf, C2),
					triple(X, rdf:type, C1),
					triple(X, rdf:type,C2),
					gen_id(['error_ ',X,' belongs to ',C1,' and ',C2],Id).

triple(Id,inc:class,C1):-
					triple(C1, owl:complementOf, C2),
					triple(X, rdf:type, C1),
					triple(X, rdf:type,C2),
					gen_id(['error_ ',X,' belongs to ',C1,' and ',C2],Id).

triple(Id,inc:class,C2):-
					triple(C1, owl:complementOf, C2),
					triple(X, rdf:type, C1),
					triple(X, rdf:type,C2),
					gen_id(['error_ ',X,' belongs to ',C1,' and ',C2],Id).

triple(Id,inc:individual,X):-
					triple(C1, owl:complementOf, C2),
					triple(X, rdf:type, C1),
					triple(X, rdf:type,C2),
					gen_id(['error_ ',X,' belongs to ',C1,' and ',C2],Id).
%%%%%%%%
%cls-svf1
%%%%%%%%
	 
triple(U, rdf:type, X):-triple(X, owl:someValuesFrom, Y),
					triple(X, owl:onProperty, P),
					triple(U,P,V),
					triple(V, rdf:type, Y). 

%%%%%%%
%cls-svf2
%%%%%%%

triple(U, rdf:type, X):-triple(X, owl:someValuesFrom, 'http://www.w3.org/2002/07/owl#Thing'),
					triple(X, owl:onProperty, P),
					triple(U,P,_).

%%%%%%%
%cls-avf
%%%%%%%

triple(V, rdf:type, Y):-triple(X, owl:allValuesFrom, Y),
				triple(X, owl:onProperty, P),
				triple(U, rdf:type, X),
				triple(U,P,V).	 

%%%%%%
%cls-hv1
%%%%%%

triple(U,P,Y):-triple(X, owl:hasValue,Y),
			triple(X, owl:onProperty,P),
			triple(U, rdf:type, X).	 

%%%%%%%%
%cls-hv2
%%%%%%

triple(U, rdf:type, X):-triple(X, owl:hasValue, Y),
					triple(X, owl:onProperty, P),
					triple(U,P,Y).

%%%%%%%%%
%cls-maxc1	
%%%%%%%%
 
triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#Inconsistency'):-
					triple(X, owl:maxCardinality, 
					literal(type('http://www.w3.org/2001/XMLSchema#nonNegativeInteger', '0'))),
					triple(X, owl:onProperty, P),
					triple(U, rdf:type, X),
					triple(U,P,_),
					gen_id(['error_ wrong cardinality ',P,' holds for ',U],Id).
					
triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#WrongCardinality'):-
					triple(X, owl:maxCardinality, 
					literal(type('http://www.w3.org/2001/XMLSchema#nonNegativeInteger', '0'))),
					triple(X, owl:onProperty, P),
					triple(U, rdf:type, X),
					triple(U,P,_),
					gen_id(['error_ wrong cardinality ',P,' holds for ',U],Id).

triple(Id,inc:property,P):-
					triple(X, owl:maxCardinality, 
					literal(type('http://www.w3.org/2001/XMLSchema#nonNegativeInteger', '0'))),
					triple(X, owl:onProperty, P),
					triple(U, rdf:type, X),
					triple(U,P,_),
					gen_id(['error_ wrong cardinality ',P,' holds for ',U],Id).

triple(Id,inc:individual,U):-
					triple(X, owl:maxCardinality, 
					literal(type('http://www.w3.org/2001/XMLSchema#nonNegativeInteger', '0'))),
					triple(X, owl:onProperty, P),
					triple(U, rdf:type, X),
					triple(U,P,_),
					gen_id(['error_ wrong cardinality ',P,' holds for ',U],Id).

%%%%%%%%
%cls-maxc2
%%%%%%%

triple(Y1, owl:sameAs, Y2):-triple(X, owl:maxCardinality, 
						literal(type('http://www.w3.org/2001/XMLSchema#nonNegativeInteger', '1'))),
						triple(X, owl:onProperty, P),
						triple(U, rdf:type, X),
						triple(U,P,Y1),
						triple(U,P,Y2),
						Y1\=Y2.
											
triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#Warning'):-	
						triple(X, owl:maxCardinality, 
						literal(type('http://www.w3.org/2001/XMLSchema#nonNegativeInteger', '1'))),
						triple(X, owl:onProperty, P),
						triple(U, rdf:type, X),
						triple(U,P,Y1),
						triple(U,P,Y2),
						Y1\=Y2,
						gen_id(['warning_ wrong cardinality ',P,' in ',U,' holds for ',Y1,' and ',Y2],Id).												
											
triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#SameIndividuals'):-	
						triple(X, owl:maxCardinality, 
						literal(type('http://www.w3.org/2001/XMLSchema#nonNegativeInteger', '1'))),
						triple(X, owl:onProperty, P),
						triple(U, rdf:type, X),
						triple(U,P,Y1),
						triple(U,P,Y2),
						Y1\=Y2,
						gen_id(['warning_ wrong cardinality ',P,' in ',U,' holds for ',Y1,' and ',Y2],Id).		

triple(Id,inc:property,P):-	
						triple(X, owl:maxCardinality, 
						literal(type('http://www.w3.org/2001/XMLSchema#nonNegativeInteger', '1'))),
						triple(X, owl:onProperty, P),
						triple(U, rdf:type, X),
						triple(U,P,Y1),
						triple(U,P,Y2),
						Y1\=Y2,
						gen_id(['warning_ wrong cardinality ',P,' in ',U,' holds for ',Y1,' and ',Y2],Id).
						
triple(Id,inc:domain,U):-	
						triple(X, owl:maxCardinality, 
						literal(type('http://www.w3.org/2001/XMLSchema#nonNegativeInteger', '1'))),
						triple(X, owl:onProperty, P),
						triple(U, rdf:type, X),
						triple(U,P,Y1),
						triple(U,P,Y2),
						Y1\=Y2,
						gen_id(['warning_ wrong cardinality ',P,' in ',U,' holds for ',Y1,' and ',Y2],Id).
						
triple(Id,inc:range,Y1):-	
						triple(X, owl:maxCardinality, 
						literal(type('http://www.w3.org/2001/XMLSchema#nonNegativeInteger', '1'))),
						triple(X, owl:onProperty, P),
						triple(U, rdf:type, X),
						triple(U,P,Y1),
						triple(U,P,Y2),
						Y1\=Y2,
						gen_id(['warning_ wrong cardinality ',P,' in ',U,' holds for ',Y1,' and ',Y2],Id).
						
triple(Id,inc:range,Y2):-	
						triple(X, owl:maxCardinality, 
						literal(type('http://www.w3.org/2001/XMLSchema#nonNegativeInteger', '1'))),
						triple(X, owl:onProperty, P),
						triple(U, rdf:type, X),
						triple(U,P,Y1),
						triple(U,P,Y2),
						Y1\=Y2,
						gen_id(['warning_ wrong cardinality ',P,' in ',U,' holds for ',Y1,' and ',Y2],Id).
						
%%%%%%%%%
%cls-maxqc1
%%%%%%%%
	 
triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#Inconsistency'):-
					triple(X, owl:maxQualifiedCardinality, 
					literal(type('http://www.w3.org/2001/XMLSchema#nonNegativeInteger', '0'))),
					triple(X, owl:onProperty, P),
					triple(X, owl:onClass, C),
					triple(U, rdf:type, X),
					triple(U,P,Y),
					triple(Y, rdf:type, C),
					gen_id(['error_ wrong cardinality ',P,' holds for ',U, '  in ',Y,' of type ',C],Id).
					
triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#WrongCardinality'):-
					triple(X, owl:maxQualifiedCardinality, 
					literal(type('http://www.w3.org/2001/XMLSchema#nonNegativeInteger', '0'))),
					triple(X, owl:onProperty, P),
					triple(X, owl:onClass, C),
					triple(U, rdf:type, X),
					triple(U,P,Y),
					triple(Y, rdf:type, C),
					gen_id(['error_ wrong cardinality ',P,' holds for ',U, '  in ',Y,' of type ',C],Id).

triple(Id,inc:property,P):-
					triple(X, owl:maxQualifiedCardinality, 
					literal(type('http://www.w3.org/2001/XMLSchema#nonNegativeInteger', '0'))),
					triple(X, owl:onProperty, P),
					triple(X, owl:onClass, C),
					triple(U, rdf:type, X),
					triple(U,P,Y),
					triple(Y, rdf:type, C),
					gen_id(['error_ wrong cardinality ',P,' holds for ',U, '  in ',Y,' of type ',C],Id).

 
					
triple(Id,inc:domain,U):-
					triple(X, owl:maxQualifiedCardinality, 
					literal(type('http://www.w3.org/2001/XMLSchema#nonNegativeInteger', '0'))),
					triple(X, owl:onProperty, P),
					triple(X, owl:onClass, C),
					triple(U, rdf:type, X),
					triple(U,P,Y),
					triple(Y, rdf:type, C),
					gen_id(['error_ wrong cardinality ',P,' holds for ',U, '  in ',Y,' of type ',C],Id).

triple(Id,inc:range,Y):-
					triple(X, owl:maxQualifiedCardinality, 
					literal(type('http://www.w3.org/2001/XMLSchema#nonNegativeInteger', '0'))),
					triple(X, owl:onProperty, P),
					triple(X, owl:onClass, C),
					triple(U, rdf:type, X),
					triple(U,P,Y),
					triple(Y, rdf:type, C),
					gen_id(['error_ wrong cardinality ',P,' holds for ',U, '  in ',Y,' of type ',C],Id).
					
 triple(Id,inc:class,C):-
					triple(X, owl:maxQualifiedCardinality, 
					literal(type('http://www.w3.org/2001/XMLSchema#nonNegativeInteger', '0'))),
					triple(X, owl:onProperty, P),
					triple(X, owl:onClass, C),
					triple(U, rdf:type, X),
					triple(U,P,Y),
					triple(Y, rdf:type, C),
					gen_id(['error_ wrong cardinality ',P,' holds for ',U, '  in ',Y,' of type ',C],Id).
					


%%%%%%%%
%cls-maxqc2
%%%%%%%

triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#Inconsistency'):-
					triple(X, owl:maxQualifiedCardinality, 
					literal(type('http://www.w3.org/2001/XMLSchema#nonNegativeInteger', '0'))),
					triple(X, owl:onProperty, P),
					triple(X, owl:onClass, 'http://www.w3.org/2002/07/owl#Thing'),
					triple(U, rdf:type, X),
					triple(U,P,_),
					gen_id(['error_ wrong cardinality ',P,' holds for ',U],Id).
			            
triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#WrongCardinality'):-
					triple(X, owl:maxQualifiedCardinality, 
					literal(type('http://www.w3.org/2001/XMLSchema#nonNegativeInteger', '0'))),
					triple(X, owl:onProperty, P),
					triple(X, owl:onClass, 'http://www.w3.org/2002/07/owl#Thing'),
					triple(U, rdf:type, X),
					triple(U,P,_),
					gen_id(['error_ wrong cardinality ',P,' holds for ',U],Id).
					
triple(Id,inc:property,P):-
					triple(X, owl:maxQualifiedCardinality, 
					literal(type('http://www.w3.org/2001/XMLSchema#nonNegativeInteger', '0'))),
					triple(X, owl:onProperty, P),
					triple(X, owl:onClass, 'http://www.w3.org/2002/07/owl#Thing'),
					triple(U, rdf:type, X),
					triple(U,P,_),
					gen_id(['error_ wrong cardinality ',P,' holds for ',U],Id).
					
triple(Id,inc:individual,U):-
					triple(X, owl:maxQualifiedCardinality, 
					literal(type('http://www.w3.org/2001/XMLSchema#nonNegativeInteger', '0'))),
					triple(X, owl:onProperty, P),
					triple(X, owl:onClass, 'http://www.w3.org/2002/07/owl#Thing'),
					triple(U, rdf:type, X),
					triple(U,P,_),
					gen_id(['error_ wrong cardinality ',P,' holds for ',U],Id).

%%%%%%%%%
%cls-maxqc3
%%%%%%%%

triple(Y1, owl:sameAs, Y2):-triple(X, owl:maxQualifiedCardinality, 
						literal(type('http://www.w3.org/2001/XMLSchema#nonNegativeInteger', '1'))),
						triple(X, owl:onProperty, P),
						triple(X, owl:onClass,C),
						triple(U, rdf:type, X),
						triple(U,P,Y1),
						triple(Y1, rdf:type, C),
						triple(U,P,Y2),
						triple(Y2, rdf:type, C),
						Y1\=Y2.
					
triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#Warning'):-
						triple(X, owl:maxQualifiedCardinality, 
						literal(type('http://www.w3.org/2001/XMLSchema#nonNegativeInteger', '1'))),
						triple(X, owl:onProperty, P),
						triple(X, owl:onClass,C),
						triple(U, rdf:type, X),
						triple(U,P,Y1),
						triple(Y1, rdf:type, C),
						triple(U,P,Y2),
						triple(Y2, rdf:type, C),
						Y1\=Y2,
						gen_id(['warning_ wrong cardinality ',P,' in ',U,' holds for ',Y1,' and ',Y2,' of type ',C],Id).						
					
triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#SameIndividuals_WrongCardinality'):-
						triple(X, owl:maxQualifiedCardinality, 
						literal(type('http://www.w3.org/2001/XMLSchema#nonNegativeInteger', '1'))),
						triple(X, owl:onProperty, P),
						triple(X, owl:onClass,C),
						triple(U, rdf:type, X),
						triple(U,P,Y1),
						triple(Y1, rdf:type, C),
						triple(U,P,Y2),
						triple(Y2, rdf:type, C),
						Y1\=Y2,
						gen_id(['warning_ wrong cardinality ',P,' in ',U,' holds for ',Y1,' and ',Y2,' of type ',C],Id).				

triple(Id,inc:property,P):-
						triple(X, owl:maxQualifiedCardinality, 
						literal(type('http://www.w3.org/2001/XMLSchema#nonNegativeInteger', '1'))),
						triple(X, owl:onProperty, P),
						triple(X, owl:onClass,C),
						triple(U, rdf:type, X),
						triple(U,P,Y1),
						triple(Y1, rdf:type, C),
						triple(U,P,Y2),
						triple(Y2, rdf:type, C),
						Y1\=Y2,
						gen_id(['warning_ wrong cardinality ',P,' in ',U,' holds for ',Y1,' and ',Y2,' of type ',C],Id).	
						
 	
triple(Id,inc:domain,U):-
						triple(X, owl:maxQualifiedCardinality, 
						literal(type('http://www.w3.org/2001/XMLSchema#nonNegativeInteger', '1'))),
						triple(X, owl:onProperty, P),
						triple(X, owl:onClass,C),
						triple(U, rdf:type, X),
						triple(U,P,Y1),
						triple(Y1, rdf:type, C),
						triple(U,P,Y2),
						triple(Y2, rdf:type, C),
						Y1\=Y2,
						gen_id(['warning_ wrong cardinality ',P,' in ',U,' holds for ',Y1,' and ',Y2,' of type ',C],Id).

		
						
triple(Id,inc:range,Y1):-
						triple(X, owl:maxQualifiedCardinality, 
						literal(type('http://www.w3.org/2001/XMLSchema#nonNegativeInteger', '1'))),
						triple(X, owl:onProperty, P),
						triple(X, owl:onClass,C),
						triple(U, rdf:type, X),
						triple(U,P,Y1),
						triple(Y1, rdf:type, C),
						triple(U,P,Y2),
						triple(Y2, rdf:type, C),
						Y1\=Y2,
						gen_id(['warning_ wrong cardinality ',P,' in ',U,' holds for ',Y1,' and ',Y2,' of type ',C],Id).

triple(Id,inc:range,Y2):-
						triple(X, owl:maxQualifiedCardinality, 
						literal(type('http://www.w3.org/2001/XMLSchema#nonNegativeInteger', '1'))),
						triple(X, owl:onProperty, P),
						triple(X, owl:onClass,C),
						triple(U, rdf:type, X),
						triple(U,P,Y1),
						triple(Y1, rdf:type, C),
						triple(U,P,Y2),
						triple(Y2, rdf:type, C),
						Y1\=Y2,
						gen_id(['warning_ wrong cardinality ',P,' in ',U,' holds for ',Y1,' and ',Y2,' of type ',C],Id).		


triple(Id,inc:class,C):-
						triple(X, owl:maxQualifiedCardinality, 
						literal(type('http://www.w3.org/2001/XMLSchema#nonNegativeInteger', '1'))),
						triple(X, owl:onProperty, P),
						triple(X, owl:onClass,C),
						triple(U, rdf:type, X),
						triple(U,P,Y1),
						triple(Y1, rdf:type, C),
						triple(U,P,Y2),
						triple(Y2, rdf:type, C),
						Y1\=Y2,
						gen_id(['warning_ wrong cardinality ',P,' in ',U,' holds for ',Y1,' and ',Y2,' of type ',C],Id).		


%%%%%%%%%
%cls-maxqc4
%%%%%%%%

triple(Y1, owl:sameAs, Y2):-triple(X, owl:maxQualifiedCardinality, 
						literal(type('http://www.w3.org/2001/XMLSchema#nonNegativeInteger', '1'))),
						triple(X, owl:onProperty, P),
						triple(X, owl:onClass, 'http://www.w3.org/2002/07/owl#Thing'),
						triple(U, rdf:type, X),
						triple(U,P,Y1),
						triple(U,P,Y2),
						Y1\=Y2.

triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#Warning'):-	
						triple(X, owl:maxQualifiedCardinality, 
						literal(type('http://www.w3.org/2001/XMLSchema#nonNegativeInteger', '1'))),
						triple(X, owl:onProperty, P),
						triple(X, owl:onClass, 'http://www.w3.org/2002/07/owl#Thing'),
						triple(U, rdf:type, X),
						triple(U,P,Y1),
						triple(U,P,Y2),
						Y1\=Y2,
						gen_id(['warning_ wrong cardinality ',P,' in ',U,' holds for ',Y1,' and ',Y2],Id).	 

triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#SameIndividuals'):-	
						triple(X, owl:maxQualifiedCardinality, 
						literal(type('http://www.w3.org/2001/XMLSchema#nonNegativeInteger', '1'))),
						triple(X, owl:onProperty, P),
						triple(X, owl:onClass, 'http://www.w3.org/2002/07/owl#Thing'),
						triple(U, rdf:type, X),
						triple(U,P,Y1),
						triple(U,P,Y2),
						Y1\=Y2,
						gen_id(['warning_ wrong cardinality ',P,' in ',U,' holds for ',Y1,' and ',Y2],Id).

triple(Id,inc:property,P):-	
						triple(X, owl:maxQualifiedCardinality, 
						literal(type('http://www.w3.org/2001/XMLSchema#nonNegativeInteger', '1'))),
						triple(X, owl:onProperty, P),
						triple(X, owl:onClass, 'http://www.w3.org/2002/07/owl#Thing'),
						triple(U, rdf:type, X),
						triple(U,P,Y1),
						triple(U,P,Y2),
						Y1\=Y2,
						gen_id(['warning_ wrong cardinality ',P,' in ',U,' holds for ',Y1,' and ',Y2],Id).
						
triple(Id,inc:domain,U):-	
						triple(X, owl:maxQualifiedCardinality, 
						literal(type('http://www.w3.org/2001/XMLSchema#nonNegativeInteger', '1'))),
						triple(X, owl:onProperty, P),
						triple(X, owl:onClass, 'http://www.w3.org/2002/07/owl#Thing'),
						triple(U, rdf:type, X),
						triple(U,P,Y1),
						triple(U,P,Y2),
						Y1\=Y2,
						gen_id(['warning_ wrong cardinality ',P,' in ',U,' holds for ',Y1,' and ',Y2],Id).

triple(Id,inc:range,Y1):-	
						triple(X, owl:maxQualifiedCardinality, 
						literal(type('http://www.w3.org/2001/XMLSchema#nonNegativeInteger', '1'))),
						triple(X, owl:onProperty, P),
						triple(X, owl:onClass, 'http://www.w3.org/2002/07/owl#Thing'),
						triple(U, rdf:type, X),
						triple(U,P,Y1),
						triple(U,P,Y2),
						Y1\=Y2,
						gen_id(['warning_ wrong cardinality ',P,' in ',U,' holds for ',Y1,' and ',Y2],Id).
						
triple(Id,inc:range,Y2):-	
						triple(X, owl:maxQualifiedCardinality, 
						literal(type('http://www.w3.org/2001/XMLSchema#nonNegativeInteger', '1'))),
						triple(X, owl:onProperty, P),
						triple(X, owl:onClass, 'http://www.w3.org/2002/07/owl#Thing'),
						triple(U, rdf:type, X),
						triple(U,P,Y1),
						triple(U,P,Y2),
						Y1\=Y2,
						gen_id(['warning_ wrong cardinality ',P,' in ',U,' holds for ',Y1,' and ',Y2],Id).

%%%%%%%%
%cls-oo
%%%%%%%

triple(Y,rdf:type,C):-triple(C,owl:oneOf,X),rdfs_member(Y,X).


%%%%%%

%%%%%%%%
%cax-sco
%%%%%%%%

triple(X, rdf:type, C2):-triple(C1, rdfs:subClassOf, C2),triple(X, rdf:type, C1).

%%%%%%%
%cax-eqc1
%%%%%%%%

triple(X, rdf:type, C2):-triple(C1, owl:equivalentClass, C2),triple(X, rdf:type, C1). 

%%%%%%%%
%cax-eqc2
%%%%%%%%
	
triple(X, rdf:type, C1):-triple(C1, owl:equivalentClass, C2),triple(X, rdf:type, C2).

%%%%%%%
%cax-dw	
%%%%%%%

triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#Inconsistency'):-
					triple(C1, owl:disjointWith, C2),
					triple(X, rdf:type, C1),
					triple(X, rdf:type, C2),
					gen_id(['error_ ',X,' belongs to ',C1,' and ',C2],Id).
			                 
triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#DisjointClasses'):-
					triple(C1, owl:disjointWith, C2),
					triple(X, rdf:type, C1),
					triple(X, rdf:type, C2),
					gen_id(['error_ ',X,' belongs to ',C1,' and ',C2],Id).

					
triple(Id,inc:class,C1):-
					triple(C1, owl:disjointWith, C2),
					triple(X, rdf:type, C1),
					triple(X, rdf:type, C2),
					gen_id(['error_ ',X,' belongs to ',C1,' and ',C2],Id).

					
					
triple(Id,inc:class,C2):-
					triple(C1, owl:disjointWith, C2),
					triple(X, rdf:type, C1),
					triple(X, rdf:type, C2),
					gen_id(['error_ ',X,' belongs to ',C1,' and ',C2],Id).

					
					
triple(Id,inc:individual,X):-
					triple(C1, owl:disjointWith, C2),
					triple(X, rdf:type, C1),
					triple(X, rdf:type, C2),
					gen_id(['error_ ',X,' belongs to ',C1,' and ',C2],Id).
					
								        

%%%%%%%%
%cax-adc
%%%%%%%

triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#Inconsistency'):-
					triple(X, rdf:type,  'http://www.w3.org/2002/07/owl#AllDisjointClasses'),
					triple(X, owl:members, Y),
					rdfs_member(Y,C1),
					rdfs_member(Y,C2),
					C1\=C2,
					triple(Z, rdf:type, C1),
					triple(Z, rdf:type, C2),
					gen_id(['error_ ',Z,' belongs to ',C1,' and ',C2],Id).


triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#DisjointClasses'):-
					triple(X, rdf:type,  'http://www.w3.org/2002/07/owl#AllDisjointClasses'),
					triple(X, owl:members, Y),
					rdfs_member(Y,C1),
					rdfs_member(Y,C2),
					C1\=C2,
					triple(Z, rdf:type, C1),
					triple(Z, rdf:type, C2),
					gen_id(['error_ ',Z,' belongs to ',C1,' and ',C2],Id).
										
triple(Id,inc:class,C1):-
					triple(X, rdf:type,  'http://www.w3.org/2002/07/owl#AllDisjointClasses'),
					triple(X, owl:members, Y),
					rdfs_member(Y,C1),
					rdfs_member(Y,C2),
					C1\=C2,
					triple(Z, rdf:type, C1),
					triple(Z, rdf:type, C2),
					gen_id(['error_ ',Z,' belongs to ',C1,' and ',C2],Id).

triple(Id,inc:class,C2):-
					triple(X, rdf:type,  'http://www.w3.org/2002/07/owl#AllDisjointClasses'),
					triple(X, owl:members, Y),
					rdfs_member(Y,C1),
					rdfs_member(Y,C2),
					C1\=C2,
					triple(Z, rdf:type, C1),
					triple(Z, rdf:type, C2),
					gen_id(['error_ ',Z,' belongs to ',C1,' and ',C2],Id).
									
triple(Id,inc:individual,Z):-
					triple(X, rdf:type,  'http://www.w3.org/2002/07/owl#AllDisjointClasses'),
					triple(X, owl:members, Y),
					rdfs_member(Y,C1),
					rdfs_member(Y,C2),
					C1\=C2,
					triple(Z, rdf:type, C1),
					triple(Z, rdf:type, C2),
					gen_id(['error_ ',Z,' belongs to ',C1,' and ',C2],Id).					

%%%%%%%

%%%%%%%%
%dt-type1
%%%%%%%%

%triple(DT, rdf:type, rdfs:datatype):-datatype(DT).

%%%%%%%%
%dt-type2
%%%%%%%%

%triple(LT,rdf:type,DT):-triple(_,_,literal(type(DT,LT))).

 
%%%%%%%
%dt-eq	
%%%%%%%

%@triple(LT1, owl:sameAs, LT2):-triple(_,_,literal(type(_,LT1))),triple(_,_,literal(type(_,LT2))),LT1=LT2.

%%%%%%%
%dt-diff
%%%%%%

%@triple(LT1, owl:differentFrom, LT2):-triple(_,_,literal(type(_,LT1))),triple(_,_,literal(type(_,LT2))),LT1\=LT2.  

%%%%%%%%
% dt-not-type
%%%%%%%%

%triple(Id,rdf:type,'http://www.semanticweb.org/inconsistency.owl#Inconsistency'):-triple(LT, rdf:type, DT),\+type(LT,DT).  

%%%%%%%%
%scm-cls
%%%%%%%

triple('http://www.w3.org/2002/07/owl#Nothing', rdfs:subClassOf, C):-
				triple(C, rdf:type, 'http://www.w3.org/2002/07/owl#Class').

%triple(C, rdf:type, 'http://www.w3.org/2002/07/owl#Class').

triple(C, rdfs:subClassOf, C):-triple(C, rdf:type, 'http://www.w3.org/2002/07/owl#Class').

triple(C, owl:equivalentClass, C):-triple(C, rdf:type, 'http://www.w3.org/2002/07/owl#Class').

triple(C, rdfs:subClassOf,  'http://www.w3.org/2002/07/owl#Thing'):-triple(C, rdf:type, 'http://www.w3.org/2002/07/owl#Class').

%%%%%%%%
% scm-sco
%%%%%%%

triple(C1, rdfs:subClassOf, C3):-triple(C1, rdfs:subClassOf, C2),  
							triple(C2, rdfs:subClassOf, C3).

%%%%%%%%%
% jesus-1
%%%%%%%%%%

triple(C1,owl:equivalentClass,C2):-triple(C2,owl:equivalentClass,C1).

%%%%%%%%%
%scm-eqc1
%%%%%%%%

triple(C2, rdfs:subClassOf, C1):-triple(C1, owl:equivalentClass, C2).

triple(C1, rdfs:subClassOf, C2):-triple(C1, owl:equivalentClass, C2).

%%%%%%%%%
% scm-eqc2
%%%%%%%%%

triple(C1, owl:equivalentClass, C2):-triple(C1, rdfs:subClassOf, C2),triple(C2, rdfs:subClassOf, C1).	 

%%%%%%%%
% scm-op
%%%%%%%

triple(P, rdfs:subPropertyOf, P):-triple(P, rdf:type,  'http://www.w3.org/2002/07/owl#ObjectProperty').

triple(P, owl:equivalentProperty, P):-triple(P, rdf:type,  'http://www.w3.org/2002/07/owl#ObjectProperty').

triple(P, rdfs:subPropertyOf, P):-triple(P, rdf:type,  'http://www.w3.org/1999/02/22-rdf-syntax-ns#Property' ).

triple(P, owl:equivalentProperty, P):-triple(P, rdf:type,  'http://www.w3.org/1999/02/22-rdf-syntax-ns#Property' ).

%%%%%%%%
% scm-dp
%%%%%%%%

triple(P, rdfs:subPropertyOf, P):-triple(P, rdf:type,  'http://www.w3.org/2002/07/owl#DatatypeProperty').	 

triple(P, owl:equivalentProperty, P):-triple(P, rdf:type,  'http://www.w3.org/2002/07/owl#DatatypeProperty').

%%%%%%%%
% scm-spo
%%%%%%%

triple(P1, rdfs:subPropertyOf, P3):-triple(P1, rdfs:subPropertyOf, P2),
							triple(P2, rdfs:subPropertyOf, P3).	 

%%%%%%%%%
%scm-eqp1
%%%%%%%%

triple(P1, rdfs:subPropertyOf, P2):-triple(P1, owl:equivalentProperty, P2).	 

triple(P2, rdfs:subPropertyOf, P1):-triple(P1, owl:equivalentProperty, P2).


%%%%%%%
% jesus
%%%%%%%%

triple(P1,owl:equivalentProperty,P2):-triple(P2,owl:equivalentProperty,P1).


%%%%%%%%%
%scm-eqp2
%%%%%%%%

triple(P1, owl:equivalentProperty, P2):-triple(P1, rdfs:subPropertyOf, P2),
								triple(P2, rdfs:subPropertyOf, P1).	 

%%%%%%%%%
% scm-dom1
%%%%%%%%

triple(P, rdfs:domain, C2):-triple(P, rdfs:domain, C1),triple(C1, rdfs:subClassOf, C2).	
 
%%%%%%%%%
%scm-dom2	
%%%%%%%%%

triple(P1, rdfs:domain, C):-triple(P2, rdfs:domain, C),triple(P1, rdfs:subPropertyOf, P2).	 

%%%%%%%%
%scm-rng1
%%%%%%%

triple(P, rdfs:range, C2):-triple(P, rdfs:range, C1),triple(C1, rdfs:subClassOf, C2).	

%%%%%%%%% 
% scm-rng2
%%%%%%%%

triple(P1, rdfs:range, C):-triple(P2, rdfs:range, C),triple(P1, rdfs:subPropertyOf, P2).

%%%%%%%%%
% scm-hv	
%%%%%%%%

triple(C1, rdfs:subClassOf, C2):-triple(C1, owl:hasValue, I),
							triple(C1, owl:onProperty, P1),
							triple(C2, owl:hasValue, I),
							triple(C2, owl:onProperty, P2),
							triple(P1, rdfs:subPropertyOf, P2). 

%%%%%%%%%%
% scm-svf1
%%%%%%%%%

triple(C1, rdfs:subClassOf, C2):-
				triple(C1, owl:someValuesFrom, Y1),
				triple(C1, owl:onProperty, P),
				triple(C2, owl:someValuesFrom, Y2),
				triple(C2, owl:onProperty, P),
				triple(Y1, rdfs:subClassOf, Y2).	 

%%%%%%%%%
% scm-svf2
%%%%%%%%

triple(C1, rdfs:subClassOf, C2):-triple(C1, owl:someValuesFrom, Y),
						triple(C1, owl:onProperty, P1),
						triple(C2, owl:someValuesFrom, Y),
						triple(C2, owl:onProperty, P2),
						triple(P1, rdfs:subPropertyOf, P2).	 

%%%%%%%%%%
%scm-avf1	
%%%%%%%%%

triple(C1, rdfs:subClassOf, C2):-triple(C1, owl:allValuesFrom, Y1),
						triple(C1, owl:onProperty, P),
						triple(C2, owl:allValuesFrom, Y2),
						triple(C2, owl:onProperty, P),
						triple(Y1, rdfs:subClassOf, Y2).	

%%%%%%%%%
% scm-avf2
%%%%%%%%%

triple(C2, rdfs:subClassOf, C1):-triple(C1, owl:allValuesFrom, Y),
						triple(C1, owl:onProperty, P1),
						triple(C2, owl:allValuesFrom, Y),
						triple(C2, owl:onProperty, P2),
						triple(P1, rdfs:subPropertyOf, P2). 

%%%%%%%%%%%
% scm-int
%%%%%%%%

triple(C, rdfs:subClassOf, D):-triple(C, owl:intersectionOf, X),
						rdfs_member(D,X).
 

%%%%%%%%
% scm-uni
%%%%%%%%%

triple(D, rdfs:subClassOf, C):-triple(C, owl:unionOf, X),
						rdfs_member(D,X).

%%%%%%






/* Systeme
 * Auteurs : Léo Cassiau, TODO vous rajoutez (désolé je connais pas vos noms)
 * Impossible de séparer processus, noms et services car leurs ensembles ont des dépendances
 * Date de création : 05/10/16
 */
MACHINE
    Systeme

SETS
    SERVICES;
    PROCESSUS;    
    NOMS;
    PROFILS = {admin, invite, usage}

VARIABLES
    services,    // Services du système
    processus,   // Processus du système
    noms,        // Noms du systèmes
    nomDe,       // Noms des services du systèmes
    contraint,   // Service contraint ou non ?
    exclusif,    // Service exclusif ou non ?
    actif,       // Service actif ou non ?
    souscrit,    // Processus inscrits au services
    profilDe,    // Profil des processus
    profilsAutorises // Profils autorises des services

INVARIANT
    services <: SERVICES
    & processus <: PROCESSUS
    & noms <: NOMS
    & contraint : services --> BOOL
    & exclusif : services --> BOOL
    & actif : services --> BOOL
    & souscrit : processus <-> services
    & profilDe: processus --> PROFILS
    & profilsAutorises : services <-> PROFILS
    & nomDe : services >->> noms
    & profilsAutorises[dom(profilsAutorises) /\ contraint~[{FALSE}]] = PROFILS // les services non contraints autorisent tous les profils de processus
    & card(profilsAutorises[dom(profilsAutorises) /\ contraint~[{TRUE}]]) >= 1 // les services contraints autorisent au moins un profil de processus
    & actif[ran(souscrit)] = {TRUE} // un processus ne peut pas être souscrit à un service désactivé
    
INITIALISATION
   actif := {} ||
   nomDe := {} ||
   contraint:= {} ||  
   exclusif := {} ||
   souscrit := {} ||
   services := {} ||
   profilDe := {} ||
   profilsAutorises := {} ||
   noms := {} ||
   processus := {}
    
OPERATIONS
    
    res <-- ajouterService(nom, cc, ee) = // Ajout du service res aux services du système. nom : nom du service, cc : service contraint ou non ?, ee : service exclusif ou non ?
    PRE
        nom : NOMS &
        cc : BOOL &
        ee : BOOL &
        nom /: nomDe[services] &
        nom /: noms
        
    THEN
        ANY ss WHERE
            ss : SERVICES &
            ss /: services
        THEN
            noms := noms \/ {nom}
            || nomDe(ss) := nom 
            || contraint(ss) := cc 
            || exclusif(ss) := ee
            || services := services \/ {ss}
            || res := ss
        END
    END;
    
    souscrire(pp, ss) = // pp processus qui souscrit au service ss
    PRE
        pp : processus &
        ss : services &
        (pp |-> ss) /: souscrit & // le processus ne doit pas être déjà souscrit au service
        actif(ss) = TRUE & // on ne peut pas souscrire à un service inactif
        ss /: (exclusif~[{TRUE}] /\ ran(souscrit))// on peut pas pas souscrire un service exclusif qui a déjà un processus souscrit
    THEN
        souscrit := souscrit \/ {(pp |-> ss)} 
    END;


    suspendre(pp, ss) = // pp processus qui suspend une souscription au service ss
    PRE
        pp : processus &
        ss : services &
        (pp |-> ss) : souscrit
    THEN
        souscrit := souscrit - {(pp |-> ss)}

    END;


    activerService(ns) = // permet d'activer un service dont le nom est donné en parametre, ns: nom du service
    PRE
        ns : noms 
        & ns : ran(nomDe) // le nom doit correspondre à un service
        & actif[nomDe~[{ns}]] = {FALSE}  // le service qui correspond au nom est non actif       
    THEN
        ANY ss WHERE                        
			ss : services
            & ss = nomDe~(ns)            
        THEN
            actif(ss) := TRUE        
        END
    END;
    
    interrompreService(ns) = // permet d'interrompre un service dont le nom est donné en parametre, ns: nom du service
    PRE
        ns : noms 
        & ns : ran(nomDe) // le nom doit correspondre à un service
        & actif[nomDe~[{ns}]] = {TRUE}  // le service qui correspond au nom est actif
    THEN
        ANY ss WHERE                        
			ss : services
            & ss = nomDe~(ns)            
        THEN
            souscrit := souscrit |>> {ss}
            || actif(ss) := FALSE
        END

    END           
    
END

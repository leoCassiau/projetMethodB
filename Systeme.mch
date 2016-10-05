/* Systeme
 * Author: 
 * Creation date: 05/10/16
 */
MACHINE
    Systeme
SETS
    PROCESSUS;
    SERVICES;
    NOMS;
    PROFILS = {admin, invite, usage}
VARIABLES 
    getNom,
    contraint,
    exclusif,
    actif,
    souscrit,
    services,
    getProfil,
    profilsAutorises
INVARIANT
    getNom : SERVICES >->> NOMS &
    contraint : SERVICES --> BOOL &
    exclusif : SERVICES --> BOOL &
    actif : SERVICES --> BOOL &
    services <: SERVICES &
    souscrit : PROCESSUS <-> services &
    getProfil: PROCESSUS --> PROFILS &
    profilsAutorises : services <-> PROFILS &
    profilsAutorises[dom(profilsAutorises) /\ contraint~[{FALSE}]] = PROFILS & // les services non contraints autorisent tous les profils de processus
    card(profilsAutorises[dom(profilsAutorises) /\ contraint~[{TRUE}]]) >= 1 &// les services contraints autorisent au moins un profil de processus
    actif[ran(souscrit)] = {TRUE} // un processus ne peut pas être souscrit à un service désactivé
    
INITIALISATION
   actif := {} ||
   getNom := {} ||
   contraint:= {} ||  
   exclusif := {} ||
   souscrit := {} ||
   services := {} ||
   getProfil := {} ||
   profilsAutorises := {}
    
OPERATIONS
    
    ajouterService(nom, cc, ee) =
    PRE
        nom : NOMS &
        cc : BOOL &
        ee : BOOL &
        nom /: getNom[services] 
        
    THEN
        ANY ss WHERE
            ss : SERVICES & 
            getNom(ss) = nom & 
            contraint(ss) = cc & 
            exclusif(ss) = ee
        THEN
            services := services \/ {ss}
        END
    END;
    
    souscrire(pp, ss) =
    PRE
        pp : PROCESSUS &
        ss : services &
        (pp |-> ss) /: souscrit & // le processus ne doit pas être déjà souscrit au service
        actif(ss) = TRUE & // on ne peut pas souscrire à un service inactif
        ss /: (exclusif~[{TRUE}] /\ ran(souscrit))// on peut pas pas souscrire un service exclusif qui a déjà un processus souscrit
    THEN
        souscrit := souscrit \/ {(pp |-> ss)} 
    END;

//suspendre une souscription de service,
    suspendre(pp, ss) =
    PRE
        pp : PROCESSUS &
        ss : services &
        (pp |-> ss) : souscrit
    THEN
        souscrit := souscrit - {(pp |-> ss)}
    END
    
END

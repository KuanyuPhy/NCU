/***************************************************************************
 *  How to use SLCIO files from HepSim, and how to build anti-KT jets
 *  S.Chekanov (ANL) chekanov@anl.gov
 *  A library for HEP events storage and processing based on Google's PB
 *  The project web site: http://atlaswww.hep.anl.gov/hepsim/
****************************************************************************/

#include<iostream>
#include<fstream>
#include<stdlib.h>

// check directory
#include <sys/stat.h>
#include <TROOT.h>
#include <TFile.h>
#include <TH1D.h>
#include <TH2D.h>
#include <TH3D.h>
#include <TProfile.h>
#include <TProfile2D.h>
#include "TMath.h"
#include "TNtupleD.h"
#include "TLorentzVector.h"

#include"time.h"
#include <dirent.h>
#include <string>
#include <vector>
#include <map>
struct stat sb;

#include "lcio.h"
#include <stdio.h>
#include "IO/LCReader.h"
#include "IMPL/LCTOOLS.h"
#include "EVENT/LCEvent.h"
#include "EVENT/LCRunHeader.h"
#include "EVENT/CalorimeterHit.h"
#include "EVENT/RawCalorimeterHit.h" 
#include "EVENT/ReconstructedParticle.h"
#include "IOIMPL/LCFactory.h"
#include "EVENT/MCParticle.h"
#include "EVENT/LCCollection.h"
#include "IMPL/LCEventImpl.h"
#include "UTIL/LCTOOLS.h"
#include "UTIL/Operators.h"
#include "UTIL/LCIterator.h"
#include "IMPL/LCCollectionVec.h"
#include "IMPL/MCParticleImpl.h"
#include "EVENT/MCParticle.h"
#include "EVENT/ReconstructedParticle.h"
#include "EVENT/Track.h"
#include "EVENT/Cluster.h"
#include "EVENT/CalorimeterHit.h"
#include "EVENT/SimCalorimeterHit.h"
#include "Objects/CartesianVector.h"
#include "Objects/Helix.h"
#include "DetectorGeometrySimple.h"
#include "IDDecoder.h"
#include "Pandora/Pandora.h"

#include "LParticle.h"
#include "CParticle.h"
using namespace std;

const double kPI   = TMath::Pi();
const double k2PI  = 2*kPI;
#include "fastjet/PseudoJet.hh"
#include "fastjet/ClusterSequence.hh"
using namespace fastjet;



float EffectiveRadius(PseudoJet Jet, vector<PseudoJet> constituents, double jetR=0.5) {
    float Energy = Jet.Et();
    float numerator = 0;
    int size=constituents.size();
    for (int i =0; i < size; i++) {
        if (Jet.delta_R(constituents[i]) > jetR) continue;
        numerator+=constituents[i].Et()*Jet.delta_R(constituents[i]);
    }
    //cout << Energy << endl;                                                     
    //cout << numerator << endl;                                                  
    return numerator/Energy;
}




float eccentricity(PseudoJet Jet, vector<PseudoJet> constituents) {
    unsigned int num=constituents.size();
    double Dphi[num], Deta[num], E[num];
    double etaSum = 0.; double phiSum = 0.; double eTot = 0.;

    for (unsigned int j=0; j< num; j++) {
        PseudoJet cp = constituents.at(j);
        E[j]=cp.e();
        Dphi[j] = Jet.phi() - cp.phi();
        // if (Dphi[j]>TMath::Pi()) Dphi[j]=2*TMath::Pi()-Dphi[j]; 
        if (fabs(Dphi[j]-2.*TMath::Pi())< fabs(Dphi[j])) Dphi[j] -= 2. * TMath::Pi();
        if (fabs(Dphi[j]+2.*TMath::Pi())< fabs(Dphi[j])) Dphi[j] += 2. * TMath::Pi();
        Deta[j] = Jet.eta() - cp.eta();
        etaSum = etaSum + Deta[j] * E[j];
        phiSum = phiSum + Dphi[j] * E[j];
        eTot   = eTot + E[j];
    }

    etaSum = etaSum/eTot; phiSum = phiSum/eTot;
    for (unsigned int j = 0; j< num; j++) {
        Deta[j] = Deta[j]-etaSum;
        Dphi[j] = Dphi[j]-phiSum;
    }


    double X1=0.;
    double X2=0;
    for (unsigned int i = 0; i < num; i++) {
        X1 += 2. * E[i] * Deta[i] * Dphi[i];
        X2 += E[i] * (Dphi[i] * Dphi[i] - Deta[i] * Deta[i]);
    }

    // variance calculations 
    double Theta = .5 * atan(X1/X2);
    double sinTheta = TMath::Sin(Theta);
    double cosTheta = TMath::Cos(Theta);
    double Theta2 = Theta + 0.5*TMath::Pi();
    double sinThetaPrime = TMath::Sin(Theta2);
    double cosThetaPrime = TMath::Cos(Theta2);



    double VarX = 0.;
    double VarY = 0.;
    for (unsigned int i = 0; i < num; i++) {
        double X=cosTheta*Deta[i] - sinTheta*Dphi[i];
        double Y=sinTheta*Deta[i] + cosTheta*Dphi[i];
        VarX += E[i]*X*X;
        VarY += E[i]*Y*Y;
    }


    double VarianceMax = VarX;
    double VarianceMin = VarY;
    if (VarianceMax < VarianceMin) {
        VarianceMax = VarY;
        VarianceMin = VarX;
    }

    double ECC=1.0 - (VarianceMin/VarianceMax);

    return ECC;

}


double nsubjettiness(PseudoJet Jet, vector<PseudoJet> constituents, int NSubJets, double jetRad=0.5) {

    //vector<CParticle> constit = jet.GetConstituents();                          
    vector<PseudoJet> jetConstit;

    unsigned int num=constituents.size();

    if (num < (unsigned int)NSubJets) {        
return -999;    
}
    TLorentzVector Jet_p;
    Jet_p.SetPxPyPzE(Jet.px(), Jet.py(), Jet.pz(), Jet.E());
    num = 0;
    for (unsigned int i=0; i< constituents.size(); i++) {
        PseudoJet c_i = constituents[i];
        if (c_i.delta_R(Jet_p) > jetRad) continue;
        jetConstit.push_back(c_i);
        num++;
    }
    if (num < (unsigned int)NSubJets) {        
return -999;    
}
    std::vector< std::vector<fastjet::PseudoJet> > kt_subjets_vec;//a vector of vectors of Pseudojets
    fastjet::JetDefinition *m_jetdef = new fastjet::JetDefinition(fastjet::kt_algorithm, 1.5, fastjet::E_scheme, fastjet::Best);
    fastjet::ClusterSequence kt_seq(jetConstit, *m_jetdef);
    delete m_jetdef;

    for (unsigned int i = 0; i < (unsigned int)NSubJets; i++) {
        kt_subjets_vec.push_back(fastjet::sorted_by_pt(kt_seq.exclusive_jets((int)NSubJets)));
    }
    double min_dist = 100000.0;
    double sum_pt   = 0.0;
    double sum_dist = 0.0;
    //first find the minimum distance.                                           
    for (unsigned int i = 0; i < jetConstit.size(); i++) {
        fastjet::PseudoJet theconstit(jetConstit[i]);
        sum_pt += theconstit.perp();
        float min_dist = 1e10;
        for (unsigned int j = 0; j < (unsigned int)NSubJets; j++) {
            const std::vector<fastjet::PseudoJet> * kt_subjets = &(kt_subjets_vec[j]\
                );
            float temp_dist =  theconstit.perp() * std::sqrt(kt_subjets->at(j).plain_distance(theconstit));
            if (temp_dist < min_dist) min_dist = temp_dist;
        } //loop over axis (subjets)                                               
        sum_dist += min_dist;
    } //loop over jet constituents                                               


    sum_dist /= (jetRad * sum_pt);


    double nSubJettiness = sum_dist;
    if (sum_dist >1.0) cout << "uh oh" << sum_dist << endl;

    return nSubJettiness;
}


double splittingscale(PseudoJet Jet) {
    if (!Jet.has_constituents())
        return -5.;

    vector<PseudoJet> jetConstit=Jet.constituents();

    double dR=Jet.associated_cluster_sequence()->jet_def().R();
    fastjet::JetDefinition *m_jetdef = new fastjet::JetDefinition(fastjet::kt_algorithm, dR, fastjet::E_scheme, fastjet::Best);

    fastjet::ClusterSequence kt_seq(jetConstit, *m_jetdef);
    delete m_jetdef;
    return dR*TMath::Sqrt(kt_seq.exclusive_dmerge(1));
}



// find all files inside a directory
std::vector<std::string> open(std::string name = "data.in") {
    vector<std::string> ntup;
    ifstream myfile;
    myfile.open(name.c_str(), ios::in);

    if (!myfile) {
        cerr << " -> Can't open input file:  " << name << endl;
        exit(1);
    }
    else {
        cout << "-> Read data file=" << name << endl;
    }

    string temp;
    while (myfile >> temp) {
        //the following line trims white space from the beginning of the string
        temp.erase(temp.begin(), std::find_if(temp.begin(), temp.end(), not1(ptr_fun<int, int>(isspace))));
        if (temp.find("#") == 0) continue;
        ntup.push_back(temp);
    }
    cout << "-> Number of files=" << ntup.size()  << endl;
    myfile.close();

    for (unsigned int i=0; i<ntup.size(); i++) {
        cout << ".. file to analyse="+ntup[i] << endl;
    }
    return ntup;
}


// main example
int main(int argc, char **argv)
{


    std::vector<std::string> files = open("data.in");
    int mtype=2; // single-particles 

   /*
    mumu="pt100";
    for(unsigned int mfile=0; mfile < files.size(); mfile++){
    string s1=files[mfile];
    if (s1.find(mumu) != std::string::npos) {
      mtype=31; //   pp 100 GeV
      break;
      }
    }

    mumu="pt3200";
    for(unsigned int mfile=0; mfile < files.size(); mfile++){
    string s1=files[mfile];
    if (s1.find(mumu) != std::string::npos) {
      mtype=32; //   pt3200
      break;
      }
    }

    mumu="pt12800";
    for(unsigned int mfile=0; mfile < files.size(); mfile++){
    string s1=files[mfile];
    if (s1.find(mumu) != std::string::npos) {
      mtype=33; //   pt3200
      break;
      }
    }

  */


    string outputfile="root/output.root";
    cout << "\n -> Output file is =" << outputfile << endl;
    TFile * RootFile = new TFile(outputfile.c_str(), "RECREATE", "Histogram file");
    TH1D * h_debug = new TH1D("debug", "events", 10, 0, 10);

    TH1D * h_pt_jet = new TH1D("jet_pt", "pt jets", 500, 0, 10);//Sorted
    h_pt_jet->GetXaxis()->SetTitle("P_{T}^{reco,jet}");
    h_pt_jet->GetYaxis()->SetTitle("Entries");
    TH1D * h_e_jet = new TH1D("jet_energy", "energy jets", 5000, 0, 1000);
    TH1D * h_eta_jet = new TH1D("jet_eta", "eta jets", 100, -0.2, 0.2);
    h_eta_jet->GetXaxis()->SetTitle("#eta");
    h_eta_jet->GetYaxis()->SetTitle("Entries");
    TH1D * h_pt_clus = new TH1D("clus_pt", "pt RecoClus", 500, 0, 10);//Recon
    h_pt_clus->GetXaxis()->SetTitle("P_{T}^{reco,jet}");
    h_pt_clus->GetYaxis()->SetTitle("Entries");
    TH1D * h_eta_clus = new TH1D("clus_eta", "eta RecoClus", 100, -0.2, 0.2);
    h_eta_clus->GetXaxis()->SetTitle("#eta");
    h_eta_clus->GetYaxis()->SetTitle("Entries");
    TH1D * h_pt_pfa = new TH1D("pfa_pt", "pt PFA", 500, 0, 10);
    TH1D * h_eta_pfa = new TH1D("pfa_eta", "eta PFA", 120, -6, 6);
    TH1D * h_pt_track = new TH1D("track_pt", "pt track", 400, 0, 1000);
    TH1D * h_eta_track = new TH1D("track_eta", "eta track", 100, -0.2, 0.2);
    h_eta_track->GetXaxis()->SetTitle("#eta");
    h_eta_track->GetYaxis()->SetTitle("Entries");

    TH1D * h_jet_n_truth = new TH1D("jet_n_truth", "Nr of truth jets", 20, 0, 20);
    TH1D * h_jet_pt_truth = new TH1D("jet_pt_truth", "pT [GeV]", 500, 0, 10);
    h_jet_pt_truth->GetXaxis()->SetTitle("P_{T}^{true,jet}");
    h_jet_pt_truth->GetYaxis()->SetTitle("Entries");
    //TH1D * h_jet_pt_truth_test = new TH1D("jet_pt_truth_test", "pT [GeV]", 200, 0, 50000);
    
    TH1D * h_jet_m_truth = new TH1D("jet_m_truth", "Mass [GeV]", 1000, 0, 1);
    TH1D * h_jetjet_m_truth = new TH1D("jetjet_m_truth", "Mass(jj) [GeV]", 500, 0, 100000);
    TH1D * h_jet_econst_truth = new TH1D("econst_truth", "Const energy", 2000, 0, 2);
    h_jet_econst_truth->GetXaxis()->SetTitle("GeV");

    TH1D * h_jet_econst_truth_sim = new TH1D("econst_truth_sim", "Const energy with Geant4 particles", 1000, 0, 500);


    // fractional energy
    //TH1D * h_jet_econst_truth_frac = new TH1D("econst_truth_frac", "Fraction of Const energy", 120, -1, 5);
    TH1D * h_jet_econst_truth_frac = new TH1D("econst_truth_frac", "Fraction of Const energy",4000, -2, 2);
    //TH1D * h_jet_econst_truth_sim_frac = new TH1D("econst_truth_sim_frac", "Fraction of Const energy with Geant4 particles", 120, -1, 5);
    TH1D * h_jet_econst_truth_sim_frac = new TH1D("econst_truth_sim_frac", "Fraction of Const energy with Geant4 particles", 4000, -2, 2);
    TH1D * h_jet_pt_truth_sim = new TH1D("jet_pt_truth_sim", "pT [GeV] plus Geant4",500, 0, 10);// plus Geant4

    //h_jet_econst_truth_frac->GetXaxis()->SetTitle("log10 (E(truth) [GeV] )");
    h_jet_econst_truth_frac->GetXaxis()->SetTitle("E(truth) [GeV] ");
    //h_jet_econst_truth_sim_frac->GetXaxis()->SetTitle("log10 (E (truth+geant4) [GeV] )");
    h_jet_econst_truth_sim_frac->GetXaxis()->SetTitle("E (truth+geant4) [GeV]");
    // fractional energy for clusters
    TH1D * h_jet_econst_clus_frac = new TH1D("econst_clus_frac", "Fraction of jet carried by cluster", 120, -1, 5);
    h_jet_econst_clus_frac->GetXaxis()->SetTitle("log10 (E(clusters) [GeV] )");

    TH1D * h_jet_pt_clus = new TH1D("jet_pt_clus", "pT(clus) [GeV]",500, 0, 10);
    TH1D * h_jet_m_clus = new TH1D("jet_m_clus", "Mass(clus) [GeV]", 100, 0, 600);
    TH1D * h_jetjet_m_clus = new TH1D("jetjet_m_clus", "Mass(jj), clusters [GeV]", 500, 0, 100000);

    TH1D * h_jet_pt_pfo = new TH1D("jet_pt_pfo", "pT(pfo) [GeV]", 200, 0, 50000);
    TH1D * h_jet_m_pfo = new TH1D("jet_m_pfo", "Mass(pfo) [GeV]", 100, 0, 600);
    TH1D * h_jetjet_m_pfo = new TH1D("jetjet_m_pfo", "Mass(jj), PFA [GeV]", 500, 0, 100000);


    // all based on clusters
    TH1D * h_jet_pt_clusters = new TH1D("jet_pt_clusters", "pT of jet clusters",500, 0, 10);
    TH1D * h_jet_n_clusters = new TH1D("jet_n_clsuters", "number of clusters in jet", 200, 0, 1000);
    TH1D * h_jet_eccent1 = new TH1D("jet_eccent1", "jet1 eccent1", 40, 0, 1.1);
    TH1D * h_jet_eccent2 = new TH1D("jet_eccent2", "jet2 eccent2", 40, 0, 1.1);
    TH1D *h_effR_j1=new TH1D("h_effR_j1", "Effective R Lead Jet", 200, 0., 1.0);
    TH1D *h_effR_j2=new TH1D("h_effR_j2", "Effective R Sub-leading Jet", 200, 0., 1.0);
    TH1D *h_d12_j1=new TH1D("h_d12_j1", "d_{12} Lead Jet", 40, 0., 400.);
    TH1D *h_d12_j2=new TH1D("h_d12_j2", "d_{12} Sub-leading Jet", 40, 0., 400.);
    TH1D *h_tau21_j1=new TH1D("h_tau21_j1", "#tau_{21} Lead Jet", 40, 0., 1.);
    TH1D *h_tau21_j2=new TH1D("h_tau21_j2", "#tau_{21} Sub-leading Jet", 40, 0., 1.);
    TH1D *h_tau32_j1=new TH1D("h_tau32_j1", "#tau_{32} Lead Jet", 40, 0., 1.);
    TH1D *h_tau32_j2=new TH1D("h_tau32_j2", "#tau_{32} Sub-leading Jet", 40, 0., 1.);


    TH1D *h_true_eccent1 = new TH1D("true_eccent1", "true eccent1", 40, 0, 1.1);
    TH1D *h_true_effR_j1=new TH1D("true_effR_j1", "Effective R Lead Jet", 400, 0., 1.0);
    TH1D *h_true_d12_j1=new TH1D("true_d12_j1", ";d_{12} Lead Jet", 40, 0., 400.);
    TH1D *h_true_tau21_j1=new TH1D("true_tau21_j1", ";#tau_{21} Lead Jet", 40, 0., 1.);
    TH1D *h_true_tau32_j1=new TH1D("true_tau32_j1", ";#tau_{32} Lead Jet", 40, 0., 1.);

    // MB ET Jets
    TH1D *h_truth_jets_const_Et = new TH1D("truth_jets_cont_Et", "truth jets const Et", 500, 0, 10);
    h_truth_jets_const_Et->GetXaxis()->SetTitle("E(truth) [GeV] ");
    TH1D *h_reco_jets_const_Et = new TH1D("reco_jets_const_Et", "reco jets const Et", 200, 0, 10);
    h_reco_jets_const_Et->GetXaxis()->SetTitle("E(reco) [GeV] ");

    TH1D *h_truth_jets_const_Et10 = new TH1D("truth_jets_cont_Et10", "truth jets const Et10", 500, 0, 10000);
    TH1D *h_reco_jets_const_Et10 = new TH1D("reco_jets_const_Et10", "reco jets const Et10", 500, 0, 10000);

    TH2D *h_jet_hitstime2D = new TH2D("jet_hitstime", "time vs hit", 100, 0.0, 3.5, 100, -5, 3);
    h_jet_hitstime2D->GetXaxis()->SetTitle("log(T [ns] )");
    h_jet_hitstime2D->GetYaxis()->SetTitle("log(E [GeV])");
    h_jet_hitstime2D->GetZaxis()->SetTitle("Sum E [GeV]");

    TH2D *h_jet_hitstime2D_ECAL = new TH2D("jet_hitstime_ecal", "time vs hit in ECAL", 100, 0.0, 3.5, 100, -5, 3);
    h_jet_hitstime2D_ECAL->GetXaxis()->SetTitle("log(T [ns] )");
    h_jet_hitstime2D_ECAL->GetYaxis()->SetTitle("log(E [GeV])");
    h_jet_hitstime2D_ECAL->GetZaxis()->SetTitle("Sum E [GeV]");

    TH1D *h_hits_time_abovecut = new TH1D("jet_hit_time_above_cut", "Time of hits above reco cut", 200, 0, 2000);
    h_hits_time_abovecut->GetXaxis()->SetTitle("Hit time [ns] )");
    h_hits_time_abovecut->GetYaxis()->SetTitle("Sum E [GeV] )");



    TH2D *h_jet_avhitstime2D = new TH2D("jet_avhitstime", "time vs hit for average", 100, 0.0, 3.5, 100, -5, 3);
    h_jet_avhitstime2D->GetXaxis()->SetTitle("log10(T^{av} [ns] )");
    h_jet_avhitstime2D->GetYaxis()->SetTitle("log10(E [GeV])");
    h_jet_avhitstime2D->GetZaxis()->SetTitle("Sum E [GeV]");


    TH1D *h_jet_hitstime_log = new TH1D("h_jet_hitstime_log", "hit time in log", 50, 0.0, 3.5);
    h_jet_hitstime_log->GetXaxis()->SetTitle("log10(T [ns] )");
    h_jet_hitstime_log->GetYaxis()->SetTitle("Sum E [GeV]");

    TH1D *h_jet_hitstime = new TH1D("h_jet_hitstime", "hit time", 200, 0.0, 2000.0);
    h_jet_hitstime->GetXaxis()->SetTitle("T [ns]");
    h_jet_hitstime->GetYaxis()->SetTitle("Sum E [GeV]");

    TH1D *h_jet_avhitstime = new TH1D("h_jet_avhitstime_log", "average hit time (over all particles)", 50, 0.0, 3.5);
    h_jet_avhitstime->GetXaxis()->SetTitle("log10(T [ns] )");
    h_jet_avhitstime->GetYaxis()->SetTitle("E [GeV]");

    TProfile *h_jet_hitstime_prof = new TProfile("h_jet_hitstime_prof", "profile hit time", 200, 0.0, 2000.0);
    h_jet_hitstime_prof->GetXaxis()->SetTitle("T [ns]");
    h_jet_hitstime_prof->GetYaxis()->SetTitle("<E [GeV]>");
    h_jet_hitstime_prof->Sumw2();

    TProfile *h_jet_hitstime_prof_log = new TProfile("h_jet_hitstime_prof_log", "profile hit time", 50, 0.0, 3.5);
    h_jet_hitstime_prof_log->GetXaxis()->SetTitle("log10 (T [ns] )");
    h_jet_hitstime_prof_log->GetYaxis()->SetTitle("<E [GeV]>");
    h_jet_hitstime_prof_log->Sumw2();

    TProfile *h_jet_hitspos_prof = new TProfile("h_jet_hitspos_prof", "profile hit time from jet center in HCAL", 40, 0.0, 400, "S");
    h_jet_hitspos_prof->GetXaxis()->SetTitle("XY distance [cm]");
    h_jet_hitspos_prof->GetYaxis()->SetTitle("< T [ns] >");
    h_jet_hitspos_prof->Sumw2();

    TProfile *h_jet_ehitspos_prof = new TProfile("h_jet_ehitspos_prof", "profile hit energy from jet center in HCAL", 40, 0.0, 400, "S");
    h_jet_ehitspos_prof->GetXaxis()->SetTitle("XY distance [cm]");
    h_jet_ehitspos_prof->GetYaxis()->SetTitle("< E(hit)[GeV] >");
    h_jet_ehitspos_prof->Sumw2();


    TProfile *h_jet_hitlayer_prof = new TProfile("h_jet_hitslayer_prof", "profile hit time per layer", 70, 0.0, 70, "S");
    h_jet_hitlayer_prof->GetXaxis()->SetTitle("HCAL layer number");
    h_jet_hitlayer_prof->GetYaxis()->SetTitle("< T [ns] >");
    h_jet_hitlayer_prof->Sumw2();

    TProfile *h_jet_hitspos_ecal_prof = new TProfile("h_jet_hitspos_ECAL_prof", "profile hit time from jet center in ECAL", 40, 0.0, 400, "S");
    h_jet_hitspos_ecal_prof->GetXaxis()->SetTitle("XY distance [cm]");
    h_jet_hitspos_ecal_prof->GetYaxis()->SetTitle("< T [ns] >");
    h_jet_hitspos_ecal_prof->Sumw2();

    TProfile *h_jet_hitlayer_ecal_prof = new TProfile("h_jet_hitslayer_ECAL_prof", "profile hit time per layer in ECAL", 40, 0.0, 40, "S");
    h_jet_hitlayer_ecal_prof->GetXaxis()->SetTitle("ECAL layer number");
    h_jet_hitlayer_ecal_prof->GetYaxis()->SetTitle("< T [ns] >");
    h_jet_hitlayer_ecal_prof->Sumw2();

    TProfile *h_jet_hitlayer_hcal_prof = new TProfile("h_jet_hitslayer_HCAL_prof", "profile hit time per layer in HCAL", 65, 0.0, 65, "S");
    h_jet_hitlayer_hcal_prof->GetXaxis()->SetTitle("HCAL layer number");
    h_jet_hitlayer_hcal_prof->GetYaxis()->SetTitle("< T [ns] >");
    h_jet_hitlayer_hcal_prof->Sumw2();

    TH1D *h_jet_energy_hit = new TH1D("jet_hit_energy", "Hit energy in jet", 200, -10, 10.);
    h_jet_energy_hit->GetXaxis()->SetTitle("log of hit energy [GeV]");
    h_jet_energy_hit->GetYaxis()->SetTitle("Events");


    TProfile *h_jet_hitdist_prof = new TProfile("h_jet_hitsloginr_prof", "Ave hit time vs distance layer 0", 72, 0, 252, "S");
    h_jet_hitdist_prof->GetXaxis()->SetTitle("Depth from layer 0 [cm]");
    h_jet_hitdist_prof->GetYaxis()->SetTitle("< T [ns] >");
    h_jet_hitdist_prof->Sumw2();



    TProfile *h_jet_ehitdist_prof = new TProfile("h_jet_ehitsloginr_prof", "Ave hit energy vs distance layer 0", 72, 0, 252, "S");
    h_jet_ehitdist_prof->GetXaxis()->SetTitle("Depth from layer 0 [cm]");
    h_jet_ehitdist_prof->GetYaxis()->SetTitle("< E(hit) [GeV] >");
    h_jet_ehitdist_prof->Sumw2();


    TH1D *h_jet_hitsjet_Trans = new TH1D("jet_hits_jet_trans", "Transverse X-Y from jet center", 80, 0, 400);
    h_jet_hitsjet_Trans->GetXaxis()->SetTitle("Transverse position [cm]");
    h_jet_hitsjet_Trans->GetYaxis()->SetTitle("Hit energy [GeV]");

    TH1D *h_jet_hitsjet_Depth = new TH1D("jet_hits_jet_depth", "Logitudinal depth from layer 0", 72, 0, 252);
    h_jet_hitsjet_Depth->GetXaxis()->SetTitle("Depth from layer 0 [cm]");
    h_jet_hitsjet_Depth->GetYaxis()->SetTitle("Hit energy [GeV]");


    TH1D *h_jet_pdg_hit300 = new TH1D("jet_hits300ns_pdg", "PDF of particles for hits>300ns", 8000, -4000, 4000);
    h_jet_pdg_hit300->GetXaxis()->SetTitle("PDG of particle for hits above 300ns");
    h_jet_pdg_hit300->GetYaxis()->SetTitle("Hit energy [GeV]");


    TH2D *h_jet_hitsjetXY = new TH2D("jet_hits_jetXY", "Energy of hits vs X - Y from jet center", 160, -400.0, 400, 160, -400, 400);
    h_jet_hitsjetXY->GetXaxis()->SetTitle("X pos [cm]");
    h_jet_hitsjetXY->GetYaxis()->SetTitle("Y pos [cm]");
    h_jet_hitsjetXY->GetZaxis()->SetTitle("Hit energy [GeV]");

    TH2D *h_jet_hitsjetXY_ECAL = new TH2D("jet_hits_jetXY_ECAL", "Energy of hits vs X - Y from jet center in ECAL", 160, -400.0, 400, 160, -400, 400);
    h_jet_hitsjetXY_ECAL->GetXaxis()->SetTitle("X pos [cm]");
    h_jet_hitsjetXY_ECAL->GetYaxis()->SetTitle("Y pos [cm]");
    h_jet_hitsjetXY_ECAL->GetZaxis()->SetTitle("ECAL Hit energy [GeV]");


    int hist_ev=0;
    static const int  nXevents = 20;
    TProfile2D *h_jet_hitsjetXY_EV[nXevents];
    for (Int_t j=0; j<nXevents; j++) {
        h_jet_hitsjetXY_EV[j] = new TProfile2D(Form("XY_time_event_%02d", j), Form("Time of hit vs XY for event %02d", j), 160, -400.0, 400, 160, -400, 400);
        h_jet_hitsjetXY_EV[j]->GetXaxis()->SetTitle("X pos [cm]");
        h_jet_hitsjetXY_EV[j]->GetYaxis()->SetTitle("Y pos [cm]");
        h_jet_hitsjetXY_EV[j]->GetZaxis()->SetTitle("Hit time [ns]");
    }

    static const int  nLayersHCAL = 64;
    static const int  nLayersECAL = 40;
    double xbins[] ={ 0.0, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10., 12., 14., 16., 18., 20., 25, 30, 40, 60, 80, 100, 200, 400, 600, 1000 };
    const int nBins=sizeof(xbins)/sizeof(double);
    TH1D *h_jet_time_layerECAL[nLayersECAL];
    TH1D *h_jet_time_layerHCAL[nLayersHCAL];
    for (Int_t j=0; j<nLayersHCAL; j++) {
        h_jet_time_layerHCAL[j] = new TH1D(Form("hcal_time_layer_%02d", j), Form("HCAL Time of hit vs for layer %02d", j), nBins-1, xbins);
        h_jet_time_layerHCAL[j]->GetXaxis()->SetTitle("Time [ns]");
        h_jet_time_layerHCAL[j]->GetYaxis()->SetTitle("Energy [GeV]");
        h_jet_time_layerHCAL[j]->Sumw2();
    }
    for (Int_t j=0; j<nLayersECAL; j++) {
        //h_jet_time_layerECAL[j] = new TH1D(Form("ecal_time_layer_%02d",j), Form("ECAL Time of hit vs for layer %02d",j),nBins-1, xbins);
        h_jet_time_layerECAL[j] = new TH1D(Form("ecal_time_layer_%02d", j), Form("ECAL Time of hit vs for layer %02d", j), 200, 0, 20.);
        h_jet_time_layerECAL[j]->GetXaxis()->SetTitle("Time [ns]");
        h_jet_time_layerECAL[j]->GetYaxis()->SetTitle("Energy");
        h_jet_time_layerECAL[j]->Sumw2();
    }

    // bin sizes
    TH1D * binsT = new TH1D("bins_time", "bins_time", nBins-1, xbins);
    binsT->Sumw2();
    for (Int_t j=0; j<nBins-1; j++) {
        float x=xbins[j+1]-xbins[j];
        binsT->Fill(xbins[j]+0.5*x, x);
    }

    TH2D *h_jet_hitsjetXY_jet = new TH2D("jet_hits_jetXY_jet", "Energy of hits vs X-Y from jet center in jet R", 160, -400.0, 400, 160, -400, 400);
    h_jet_hitsjetXY_jet->GetXaxis()->SetTitle("X pos [cm]");
    h_jet_hitsjetXY_jet->GetYaxis()->SetTitle("Y pos [cm]");
    h_jet_hitsjetXY_jet->GetZaxis()->SetTitle("Hit energy [GeV]");



    TProfile2D *h_jet_hitsjetXY_prof1 = new TProfile2D("jet_hits_jetXY_prof1", "Av hit energy vs X-Y from jet center", 160, -400.0, 400, 160, -400, 400);
    h_jet_hitsjetXY_prof1->GetXaxis()->SetTitle("X pos [cm]");
    h_jet_hitsjetXY_prof1->GetYaxis()->SetTitle("Y pos [cm]");
    h_jet_hitsjetXY_prof1->GetZaxis()->SetTitle("<energy of hit>  [GeV]");

    TProfile2D *h_jet_hitsjetXY_prof2 = new TProfile2D("jet_hits_jetXY_prof2", "Av hit time vs X and Y from jet center", 160, -400.0, 400, 160, -400, 400);
    h_jet_hitsjetXY_prof2->GetXaxis()->SetTitle("X pos [cm]");
    h_jet_hitsjetXY_prof2->GetYaxis()->SetTitle("Y pos [cm]");
    h_jet_hitsjetXY_prof2->GetZaxis()->SetTitle("<Time>  [ns]");


    TProfile2D *h_jet_hitsjetXY_ECAL_prof2 = new TProfile2D("jet_hits_jetXY_ECAL_prof2", "Av hit time vs X and Y from jet center in ECAL", 160, -400.0, 400, 160, -400, 400);
    h_jet_hitsjetXY_ECAL_prof2->GetXaxis()->SetTitle("X pos [cm]");
    h_jet_hitsjetXY_ECAL_prof2->GetYaxis()->SetTitle("Y pos [cm]");
    h_jet_hitsjetXY_ECAL_prof2->GetZaxis()->SetTitle("<Time>  [ns]");



    TH2D *h_jet_hitsRLE = new TH2D("jet_hits_propogration_rle", "R vs L for hit energy", 80, 0.0, 400, 72, 0, 252);
    h_jet_hitsRLE->GetXaxis()->SetTitle("Transverse  distance [cm]");
    h_jet_hitsRLE->GetYaxis()->SetTitle("Depth from layer 0 [cm]");
    h_jet_hitsRLE->GetZaxis()->SetTitle("Hit energy [GeV]");

    TProfile2D *h_jet_hitsRLT = new TProfile2D("jet_hits_propogration_rlt_prof", "R vs L vs Time", 80, 0.0, 400, 72, 0, 252, "S");
    h_jet_hitsRLT->GetXaxis()->SetTitle("Trans distance [cm]");
    h_jet_hitsRLT->GetYaxis()->SetTitle("Depth from layer 0 [cm]");
    h_jet_hitsRLT->GetZaxis()->SetTitle("<Time> [ns]");

    TH1D * h_jet_hits_energy_frac = new TH1D("h_jet_hit_energy_frac", "Fraction of hit energy", 200, -6, 5);
    h_jet_hits_energy_frac->GetXaxis()->SetTitle("log10 (E [hit] )");

    TH1D * h_jet_hits_energytime_frac = new TH1D("h_jet_hits_energytime_frac", "Fraction of hit energy vs time", 100, 0, 3.5);
    h_jet_hits_energytime_frac->GetXaxis()->SetTitle("log10 (T [ns] )");


    // jet resolution
    static int nmax=16;
    TH1D *h_jet_res[nmax];
    TH1D *h_jet_ptr[nmax];
    for (int j=0; j<nmax; j++) {
        h_jet_res[j] = new TH1D(Form("jet_resolution_%02d", j), Form("jets_res_%02d", j), 160, 0.0, 2.0);
        h_jet_ptr[j] = new TH1D(Form("jet_resolution_pt_%02d", j), Form("jets_res_pt_%02d", j), 1000, 0, 50000);
        h_jet_res[j]->Sumw2();
    }

    TH1D *h_jet_res_hits[nmax];
    TH1D *h_jet_ptr_hits[nmax];
    for (int j=0; j<nmax; j++) {
        h_jet_res_hits[j] = new TH1D(Form("jet_resolution_hits_%02d", j), Form("jets_res_hits_%02d", j), 160, 0.0, 2.0);
        h_jet_ptr_hits[j] = new TH1D(Form("jet_resolution_hits_pt_%02d", j), Form("jets_res_hits_pt_%02d", j), 1000, 0, 50000);
        h_jet_res_hits[j]->Sumw2();
    }

    TH1D *h_jet_res_hits_raw[nmax];
    TH1D *h_jet_ptr_hits_raw[nmax];
    for (int j=0; j<nmax; j++) {
        h_jet_res_hits_raw[j] = new TH1D(Form("jet_resolution_hits_raw_%02d", j), Form("jets_res_hits_raw_%02d", j), 160, 0.0, 2.0);
        h_jet_ptr_hits_raw[j] = new TH1D(Form("jet_resolution_hits_raw_pt_%02d", j), Form("jets_res_hits_raw_pt_%02d", j), 1000, 0, 50000);
        h_jet_res_hits_raw[j]->Sumw2();
    }

    // raw hits corrected by appropriate sampleing fraction (SF)
    TH1D *h_jet_res_hits_raw_sf[nmax];
    TH1D *h_jet_ptr_hits_raw_sf[nmax];
    //TH2D *h_jet_res_hitstime[nmax];

    for (int j=0; j<nmax; j++) {
        h_jet_res_hits_raw_sf[j] = new TH1D(Form("jet_resolution_hits_raw_sf_%02d", j), Form("jets_res_hits_raw_sf_%02d", j), 160, 0.0, 2.0);
        h_jet_ptr_hits_raw_sf[j] = new TH1D(Form("jet_resolution_hits_raw_sf_pt_%02d", j), Form("jets_res_hits_raw_sf_pt_%02d", j), 1000, 0, 50000);
        h_jet_res_hits_raw_sf[j]->Sumw2();
        //h_jet_res_hitstime[j] = new TH2D(Form("jet_resolution_hitstime_%02d",j), Form("jets_res_hitstime_%02d",j),1000,0.0,0.0001,200,0,2000);

    }

    // track resolution
    TH1D *h_track_res[nmax];
    TH1D *h_track_ptr[nmax];
    for (int j=0; j<nmax; j++) {
        int nbins=2000-10*j*j; // decreasing number of bins  
        if (nbins<0) nbins=20;
        h_track_res[j] = new TH1D(Form("track_resolution_%02d", j), Form("track_res_%02d", j), nbins, 0.0, 2.0);
        h_track_ptr[j] = new TH1D(Form("track_resolution_pt_%02d", j), Form("track_res_pt_%02d", j), 1000, 0, 50000);
        h_track_res[j]->Sumw2();
    }


    // read detector geometry for this configuration 
    string detector="./data/rfull009_sifcch7/sifcch7/sifcch7.pandora";
    DetectorGeometrySimple* geom = new   DetectorGeometrySimple(detector);
    string caloType="HAD_BARREL";
    DetectorGeometrySimple::ExtraSubDetectorParameters* xsubdet = geom->getExtraSubDetectorParametersFromType(caloType);
    if (xsubdet == NULL) {
        std::cout << "The ExtraSubDetectorParameters for " << caloType << " were not found." << std::endl;
        throw new std::exception;
    }


    string caloType_ecal="EM_BARREL";
    DetectorGeometrySimple::ExtraSubDetectorParameters* xsubdet_ecal = geom->getExtraSubDetectorParametersFromType(caloType_ecal);
    if (xsubdet_ecal == NULL) {
        std::cout << "The ExtraSubDetectorParameters for " << caloType_ecal << " were not found." << std::endl;
        throw new std::exception;
    }



    // Get the decoder.
    IDDecoder* decoder = xsubdet->m_decoder;
    IDDecoder* decoder_ecal = xsubdet_ecal->m_decoder;

    // calculate position
    double layer_size_mm=27.5+5+2.5;
    double hcal_inner_R_mm=2300;

    double layer_size_ecal_mm=4.0;
    double ecal_inner_R_mm=2100;



    // calculate weighted average of time
    double XTime=0;
    double XEnergy=0;



    //pandora::Pandora* m_pandora = new pandora::Pandora();
    //m_pandora->ReadSettings(detector);

    const pandora::SubDetectorType subDetectorType = geom->getPandoraSubDetectorType(caloType);
    //const pandora::SubDetector &subdet(pandora.GetGeometry()->GetSubDetector(subDetectorType));

  /*
      const pandora::SubDetectorType subDetectorType(geom->getPandoraSubDetectorType(caloType));
      double innerRCoordinate=subdet->m_innerRCoordinate.Get();
      double nLayers=subdet->subdet->m_nLayers.Get();
      cout << "Detector=" << caloType << endl;
      cout << "innerRCoordinate (mm)=" << innerRCoordinate << endl;
      cout << "nLayers=" << nLayers  << endl;
  */

  // pandora::Pandora* pandora = new pandora::Pandora();
  //const pandora::SubDetector &subdet(pandora->GetGeometry()->GetSubDetector(subDetectorType));
  //  PandoraApi::Geometry::LayerParametersList layer_par= xsubdet->m_layerParametersList;


    const char* tupleNames = "px:py:pz:vx:vy:vz:ex:ey:ez:pdg:np:nd:gs:ss";
    TNtupleD *tuple= new TNtupleD("MCParticle", "", tupleNames);



    double  minPtConst=0.2; // min pT on constituents
    // jets
    double  Rparam = 0.5;
    const double ETAmax =1.0;
    double  ETmin=0.5;
    if (mtype==1) ETmin=200; // increase for boosted
    if (mtype==31)  ETmin=50;
    if (mtype==32)  ETmin=2000;
    if (mtype==33)  ETmin=8000;


    if (mtype==1)   cout << "mu+mu- mode for boosted jets" << endl;
    if (mtype==2)   cout << "single-particle mode for pgun" << endl;
    if (mtype==3)   cout << "pp mode for jet resolutions" << endl;

    cout << "min PT for jets=" << ETmin << endl;
    cout << "eta max for jets=" << ETAmax << endl;
    cout << "R for jets =" << Rparam << endl;

    // fastjet
    Strategy strategy = fastjet::Best;
    JetDefinition jet_def(fastjet::antikt_algorithm, Rparam, strategy);
    //JetDefinition jet_def(fastjet::kt_algorithm, Rparam, strategy);
    //JetDefinition jet_def(fastjet::cambridge_algorithm, Rparam, strategy);
    //JetDefinition jet_def(fastjet::antikt_algorithm, Rparam, strategy);

  //   E_scheme=0,
  //   pt_scheme=1,
  //   pt2_scheme=2,
  //   Et_scheme=3,
  //  Et2_scheme=4,
    // JetDefinition jet_def(fastjet::ee_genkt_algorithm, Rparam, 0,  strategy); 
    //JetDefinition jet_def(fastjet::ee_kt_algorithm); 

   // return 0;


    //double m,px,py,pz,e,vx,vy,vz,ex,ey,ez ;
    //int pdg,np,nd,gs,ss ;

    int MaxEvents=100000000;

    int nEvents = 0;

    // loop over all files
    for (unsigned int mfile=0; mfile < files.size(); mfile++) {
        string Rfile=files[mfile];

        cout <<  " # File=" << Rfile << endl;

        IO::LCReader* lcReader = IOIMPL::LCFactory::getInstance()->createLCReader();
        lcReader->open(Rfile.c_str());

        EVENT::LCEvent* evt=0;

        if (nEvents>MaxEvents) break;

        //----------- the event loop -----------
        while ((evt = lcReader->readNextEvent()) != 0) {
            if (nEvents==0) UTIL::LCTOOLS::dumpEvent(evt);

            // UTIL::LCTOOLS::dumpEvent( evt ) ;

            nEvents++;
            if ((nEvents<100 && nEvents%10==0) || (nEvents>100 && nEvents%200==0))
                cout <<  " # Events=" << nEvents << endl;


            if (nEvents>MaxEvents) break;


            h_debug->Fill(1.0);

            std::string mcpName("MCParticle");
            // get truth
            IMPL::LCCollectionVec* col = (IMPL::LCCollectionVec*) evt->getCollection(mcpName);
            int nMCP = col->getNumberOfElements();

            int neu=0;

            vector<PseudoJet> avec_truth;     // created by generator 
            vector<PseudoJet> avec_truth_sim; // also created by geant 

            for (int i=0; i<nMCP; ++i) {
                EVENT::MCParticle* mcp =  (EVENT::MCParticle*) col->getElementAt(i);
                double px = mcp->getMomentum()[0];
                double py = mcp->getMomentum()[1];
                double pz = mcp->getMomentum()[2];
                double m = mcp->getMomentum()[3];
                double e=sqrt(px*px+py*py+pz*pz+m*m);

                //cout << "m=" << m << " |p|=" << sqrt(px*px+py*py+pz*pz) << " e=" << e << endl;

                TLorentzVector p;
                p.SetPxPyPzE(px, py, pz, e);

                // find high-pT neutrino
                if ((mcp->getPDG() == 12 || mcp->getPDG() == 14 || mcp->getPDG() == 16) && p.Pt()>100) {
                    neu++;
                }

                // includes Geant4 and backscatter too
                bool isGeant4=false;
                if (abs(p.PseudoRapidity()) < 2.0 && (mcp->isCreatedInSimulation()==true || mcp->isBackscatter() ==true) && p.Pt()>minPtConst) {
                    if (mcp->getPDG() != 12 && mcp->getPDG() != 14 && mcp->getPDG() != 16) isGeant4=true;
                }

                // generator-level 
                bool isGen=false;
                if (abs(p.PseudoRapidity()) < 2.0 && mcp->getGeneratorStatus()==1 && p.Pt()>minPtConst) {
                    if (mcp->getPDG() != 12 && mcp->getPDG() != 14 && mcp->getPDG() != 16) isGen=true;
                }



                // only generator level
                if (isGen==true) {
                    int pdg = mcp->getPDG();
                    int np = mcp->getParents().size();
                    int nd = mcp->getDaughters().size();
                    int gs = mcp->getGeneratorStatus();
                    int ss = mcp->getSimulatorStatus();
                    //cout << mcp->getSimulatorStatus() << " " << mcp->getPDG() << endl;
                    //tuple->Fill(px,py,pz,vx,vy,vz,ex,ey,ez,pdg,np,nd,gs,ss) ;
                    avec_truth.push_back(PseudoJet(px, py, pz, e));
                    //cout << pdg << " " << px << " " << py << " " << pz << " " << e << endl;
                }

                // plus Geant4
                if (isGen==true || isGeant4==true) {
                    int pdg = mcp->getPDG();
                    int np = mcp->getParents().size();
                    int nd = mcp->getDaughters().size();
                    int gs = mcp->getGeneratorStatus();
                    int ss = mcp->getSimulatorStatus();
                    //cout << mcp->getSimulatorStatus() << " " << mcp->getPDG() << endl;
                    //tuple->Fill(px,py,pz,vx,vy,vz,ex,ey,ez,pdg,np,nd,gs,ss) ;
                    avec_truth_sim.push_back(PseudoJet(px, py, pz, e));
                    //cout << pdg << " " << px << " " << py << " " << pz << " " << e << endl;
                }

            }


            //cout << avec_truth_sim.size() << " gen=" << avec_truth.size() << endl;


            // assume remnant for mu+mu-
            if (mtype==1) {
                avec_truth.push_back(PseudoJet(0, 0, 5000, 5000));
                avec_truth.push_back(PseudoJet(0, 0, -5000, 5000));
            }



            ClusterSequence clust_seq(avec_truth, jet_def);
            vector<PseudoJet> jets_truth = clust_seq.inclusive_jets(ETmin);
            vector<PseudoJet> sjets_truth = sorted_by_pt(jets_truth);
            //cout << "Njet=" << jets_truth.size() << endl;
            vector<LParticle> truthjets;
            int nn=0;
            for (unsigned int k = 0; k<sjets_truth.size(); k++) {
                double eta=sjets_truth[k].pseudorapidity();
                double phi=sjets_truth[k].phi();
                if (phi<0)  phi = phi + k2PI;
                double m=jets_truth[k].m();
                double pt = sjets_truth[k].perp();
                double e = sjets_truth[k].e();

                //TLorentzVector p;
                //p.SetPxPyPzE(px,py,pz,e);
                if (pt < ETmin)                    continue;
                if (fabs(eta)> ETAmax)            continue;
                LParticle p(sjets_truth[k].px(), sjets_truth[k].py(), sjets_truth[k].pz(), sjets_truth[k].e(), 0);

                // fill jet substructure
                p.SetParameter(EffectiveRadius(sjets_truth[k], sjets_truth[k].constituents(), Rparam)); // 0 
                p.SetParameter(nsubjettiness(sjets_truth[k], sjets_truth[k].constituents(), 1, Rparam)); // 1 
                p.SetParameter(nsubjettiness(sjets_truth[k], sjets_truth[k].constituents(), 2, Rparam)); // 2 
                p.SetParameter(nsubjettiness(sjets_truth[k], sjets_truth[k].constituents(), 3, Rparam)); //  3 
                p.SetParameter(splittingscale(sjets_truth[k])); // 4 
                p.SetParameter(eccentricity(sjets_truth[k], sjets_truth[k].constituents())); // 5
                truthjets.push_back(p);


                //MB Truth Jets
                //one jet per event
                vector<PseudoJet> constit=sjets_truth[k].constituents();
                int csize=constit.size();
                for (int i=0; i<csize; i++) {
                    // std::cout << "Truth Jets const.Et(): " << (constit[i].Et()) << std::endl;
                    h_jet_econst_truth->Fill(constit[i].e(), constit[i].e());
                    cout<<"h_jet_econst_truth ="<<constit[i].e()<<endl;
                    //h_jet_econst_truth_frac->Fill(TMath::Log10(constit[i].e()), constit[i].e()/e);
                    h_jet_econst_truth_frac->Fill(constit[i].e(), constit[i].e()/e);
                    //cout<<"h_jet_econst_truth_frac ="<<TMath::Log10(constit[i].e())<<endl;
                    cout<<"h_jet_econst_truth_frac ="<<constit[i].e()<<endl;
                    h_truth_jets_const_Et->Fill(constit[i].Et());
                }

                if (pt >= 10000) {
                    for (int i=0; i<csize; i++) {
                        // std::cout << "Truth Jets const.Eti20(): " << (constit[i].Et()) << std::endl;
                        h_truth_jets_const_Et10->Fill(constit[i].Et());
                    }
                }


                // cout << "jet=" << nn << " E=" << e << " eta=" << eta << " phi=" << phi <<  endl;
                nn++;
                if (nn>2) break; // take first 3 jets

            }


            // includes Geant4
            ClusterSequence clust_seq1(avec_truth_sim, jet_def);
            vector<PseudoJet> jets_truth_sim = clust_seq1.inclusive_jets(ETmin);
            vector<PseudoJet> sjets_truth_sim = sorted_by_pt(jets_truth_sim);
            //cout << "Njet=" << jets_truth.size() << endl;
            nn=0;
            for (unsigned int k = 0; k<sjets_truth_sim.size(); k++) {
                double eta=sjets_truth_sim[k].pseudorapidity();
                double phi=sjets_truth_sim[k].phi();
                if (phi<0)  phi = phi + k2PI;
                double m=jets_truth_sim[k].m();
                double pt = sjets_truth_sim[k].perp();
                double e = sjets_truth_sim[k].e();
                h_jet_pt_truth_sim->Fill(pt);
                cout <<"jet_pt_truth_sim ="<<pt<<endl;

                //TLorentzVector p;
                //p.SetPxPyPzE(px,py,pz,e);
                if (pt < ETmin)                    continue;
                if (fabs(eta)> ETAmax)            continue;
                LParticle p(sjets_truth_sim[k].px(), sjets_truth_sim[k].py(), sjets_truth_sim[k].pz(), sjets_truth_sim[k].e(), 0);
                vector<PseudoJet> constit=sjets_truth_sim[k].constituents();
                int csize=constit.size();
                for (int i=0; i<csize; i++) {
                    h_jet_econst_truth_sim->Fill(constit[i].e(), constit[i].e());
                    //h_jet_econst_truth_sim_frac->Fill(TMath::Log10(constit[i].e()), constit[i].e()/e);
                    h_jet_econst_truth_sim_frac->Fill(constit[i].e(), constit[i].e()/e);
                    cout<<"econst_truth_sim_frac ="<<constit[i].e()<<endl;
                }
                nn++;
                if (nn>2) break; // take first 3 jets
            }




            // skip semileptonic decays for WW studies only
            //if (neu>0) continue;
            // cout << neu << " " << truthjets.size() << endl;

            if (truthjets.size() >1) {
                // cout << "Nr of jets=" << truthjets.size() << endl;
                for (unsigned int j=0; j<truthjets.size(); j++) {
                    LParticle p=(LParticle)truthjets.at(j);
                    TLorentzVector L= p.GetP();
                    double pt =  L.Perp();
                    double eta =  L.Eta();
                    double mass =  L.M();
                }
                LParticle L1=(LParticle)truthjets.at(0);
                LParticle L2=(LParticle)truthjets.at(1);
                TLorentzVector LL=L1.GetP()+L2.GetP();
                h_jetjet_m_truth->Fill(LL.M());
            }



            // fill jet substructure first
            // intrested in 2 leading jets only!
            h_jet_n_truth->Fill(truthjets.size());
            //cout << "Nr of truth jets=" << truthjets.size() << endl;

            for (unsigned int j=0; j<truthjets.size(); j++) {
                LParticle p=(LParticle)truthjets.at(j);
                TLorentzVector L= p.GetP();
                double pt =  L.Perp();
                double eta =  L.Eta();
                double mass =  L.M();
                //cout<<"pt= "<<pt<<endl;
                h_jet_pt_truth->Fill(pt);
                cout <<"jet_pt_truth ="<<pt<<endl;
                
                h_jet_m_truth->Fill(mass);
                cout <<"jet_m_truth ="<<mass<<endl;

                vector<double> par1=p.GetParameters();
                double jet1_tau32=par1[3]/par1[2];
                double jet1_tau21=par1[2]/par1[1];
                double jet1_d12=par1[4];
                double jet1_effR_cut=par1[0];
                float ecc1=par1[5];    // eccentricity
                h_true_eccent1->Fill(ecc1);
                h_true_effR_j1->Fill(jet1_effR_cut);
                h_true_tau21_j1->Fill(jet1_tau21);
                h_true_tau32_j1->Fill(jet1_tau32);
                h_true_d12_j1->Fill(jet1_d12);
                if (j>1) break; // take 2 jets only 
            }





            double xsum=0;

            // Pandora PFA 
            // look up at: /share/sl6/ilcsoft/slic/release-v05-00-00/slicPandora/HEAD/lcio/v02-04-03/build/include/EVENT
            vector<PseudoJet> avec_pfo;
            IMPL::LCCollectionVec* col2 = (IMPL::LCCollectionVec*) evt->getCollection("PandoraPFOCollection");
            int nPFO = col2->getNumberOfElements();
            for (int i=0; i<nPFO; ++i) {
                EVENT::ReconstructedParticle* mcp =  (EVENT::ReconstructedParticle*) col2->getElementAt(i);
                double px = mcp->getMomentum()[0];
                double py = mcp->getMomentum()[1];
                double pz = mcp->getMomentum()[2];
                double m = 0; // mcp->getMomentum()[3];
                double e=sqrt(px*px+py*py+pz*pz+m*m);

                PseudoJet pp(px, py, pz, e);
                double eta_r=pp.pseudorapidity();
                double phi_r=pp.phi();
                double pt_r=pp.pt();
                // fill clusters 
                h_pt_pfa->Fill(pt_r);
                h_eta_pfa->Fill(eta_r);


                if (pp.pt()>minPtConst)avec_pfo.push_back(pp);
                //cout << m << " " << e << endl;
            }

            // ----------------- PFO jets --------------------------
            ClusterSequence clust_seq_pfo(avec_pfo, jet_def);
            vector<PseudoJet> jets_pfo = clust_seq_pfo.inclusive_jets(ETmin);
            vector<PseudoJet> sjets_pfo = sorted_by_pt(jets_pfo);
            vector<LParticle> pfojets;
            for (unsigned int k = 0; k<sjets_pfo.size(); k++) {
                double eta=sjets_pfo[k].pseudorapidity();
                double phi=sjets_pfo[k].phi();
                if (phi<0)  phi = phi + k2PI;
                double m=jets_pfo[k].m();
                double pt = sjets_pfo[k].perp();
                double e = sjets_pfo[k].e();
                if (pt < ETmin)                    continue;
                if (fabs(eta)> ETAmax)            continue;
                LParticle p(sjets_pfo[k].px(), sjets_pfo[k].py(), sjets_pfo[k].pz(), sjets_pfo[k].e(), 0);
                pfojets.push_back(p);
            }

            if (pfojets.size() >1) {
                // cout << "Nr of PFO jets=" << pfojets.size() << endl;
                for (unsigned int j=0; j<pfojets.size(); j++) {
                    LParticle p=(LParticle)pfojets.at(j);
                    TLorentzVector L= p.GetP();
                    double pt =  L.Perp();
                    double eta =  L.Eta();
                    double mass =  L.M();
                    //cout << mass << endl;
                    h_jet_pt_pfo->Fill(pt);
                    h_jet_m_pfo->Fill(mass);
                }
                LParticle L1=(LParticle)pfojets.at(0);
                LParticle L2=(LParticle)pfojets.at(1);
                TLorentzVector LL=L1.GetP()+L2.GetP();
                h_jetjet_m_pfo->Fill(LL.M());
            }



            //tracks 
            // look up at: /share/sl6/ilcsoft/slic/release-v05-00-00/slicPandora/HEAD/lcio/v02-04-03/build/include/EVENT
          /*
            IMPL::LCCollectionVec* col3 = (IMPL::LCCollectionVec*) evt->getCollection( "Tracks"  ) ;
            int nTRK = col3->getNumberOfElements() ;
              for(int i=0 ; i<nTRK ; ++i){
                EVENT::Track* mcp =  (EVENT::Track*) col3->getElementAt(i) ;
                //float* pos= col3->getPosition();
                //px = mcp->getMomentum()[0] ;
                //py = mcp->getMomentum()[1] ;
                //pz = mcp->getMomentum()[2] ;
            }
          */


            double calo_sum=0;
            // clusters
            vector<PseudoJet> avec_clus;
            double xsum_cl=0;
            IMPL::LCCollectionVec* col5 = (IMPL::LCCollectionVec*) evt->getCollection("ReconClusters");
            int nCL = col5->getNumberOfElements();
            for (int i=0; i<nCL; ++i) {
                EVENT::Cluster* mcp =  (EVENT::Cluster*) col5->getElementAt(i);
                const float* pos= mcp->getPosition();
                float x=pos[0];
                float y=pos[1];
                float z=pos[2];
                double e = mcp->getEnergy();
                double _tmp = std::sqrt(x*x + y*y + z*z);
                double px =  e*x/_tmp;
                double py =  e*y/_tmp;
                double pz =  e*z/_tmp;


                calo_sum=calo_sum+e;


                //double theta=mcp->getITheta();
                //double phi=mcp->getIPhi();
                //double eta=-log(tan(0.5*theta));
                //double et=e*sin(theta);

                //if (e<0.1) continue; // min energy
                //double pz=e*cos(theta);
                //double px=et*cos(theta);
                //double py=et*sin(theta);
                PseudoJet pj(px, py, pz, e);
                double eta_r=pj.pseudorapidity();
                double phi_r=pj.phi();
                double pt_r=pj.pt();
                // fill clusters 
                h_pt_clus->Fill(pt_r);
                cout <<"clus_pt ="<<pt_r<<endl;
                h_eta_clus->Fill(eta_r);

                //cout << " e=" << e <<  " phi=" << pj.phi() << " eta=" << pj.eta() << endl;
                if (pt_r>minPtConst) avec_clus.push_back(pj);

            }


            // cout << "Calo clus sum=" << calo_sum << endl;



            // HCAL simulated raw hits
            double hcalsum_raw=0;
            vector<PseudoJet> avec_hits_raw;
            vector<double> avec_hittime_raw;
            vector<PseudoJet> avec_hits_raw_sf;
            vector<LParticle> simhits;

            IMPL::LCCollectionVec* col50 = (IMPL::LCCollectionVec*) evt->getCollection("HcalBarrelHits");
            //IMPL::LCCollectionVec* col50 = (IMPL::LCCollectionVec*) evt->getCollection("HAD_BARREL") ;
            nCL = col50->getNumberOfElements();
            for (int i=0; i<nCL; ++i) {
                EVENT::SimCalorimeterHit* mcp =  (EVENT::SimCalorimeterHit*) col50->getElementAt(i);
                // EVENT::CalorimeterHit* mcp =  (EVENT::CalorimeterHit*) col50->getElementAt(i) ;
                const float* pos= mcp->getPosition();
                float x=pos[0];
                float y=pos[1];
                float z=pos[2];
                double e = mcp->getEnergy();
                double Thit=mcp->getTimeCont(0);

                // Get the two 32-bit chunks of the ID.
                int cellId0 = mcp->getCellID0();
                int cellId1 = mcp->getCellID1();
                // Make a 64-bit id for the IDDecoder.  The type MUST be "long long" and not "long".  (from Tony Johnson)
                long long cellId = ((long long)cellId1) << 32 | cellId0;
                // cout << cellId << " time=" << Thit << endl; 
                // int layer = decoder->getFieldValue("layer", cellId);
                // Decode the layer number from the ID.
                int layer = decoder->getFieldValue("layer", cellId);
                //cout << "layer=" << layer << endl;

               //DetectorGeometrySimple::ExtraLayerParameters xlayerParams = xsubdet->m_extraLayerParams.at(layer);
               //double samplingFraction = xlayerParams.m_samplingFraction.Get();
               //PandoraApi::Geometry::LayerParameters lp =  xsubdet->layerParams.at(layer);
               //double closestDistanceToIp = xlayerParams.m_closestDistanceToIp.Get();
               //double InteractionLength=xlayerParams.m_nInteractionLengths.Get();
               //double RadiationLength = m_nRadiationLengths.Get();
               //cout << layer << " " << closestDistanceToIp << endl;


               // position from 0-63 layer
               // 1st layer on middle
                double layer_pos_cm=0.1*(layer_size_mm*0.5+(layer*layer_size_mm));

                // number of MC contributions to the hit
                // calculate average time  in [ns] 
                double avt = 0; double ave=0;
                for (int jj=0; jj<mcp->getNMCContributions(); jj++) {
                    avt=avt+mcp->getEnergyCont(jj)*mcp->getTimeCont(jj);
                    ave=ave+mcp->getEnergyCont(jj);
                }
                avt=avt/ave;



                double Rpos_cm=0.1*std::sqrt(x*x+y*y);
                double _tmp = std::sqrt(x*x + y*y + z*z);
                double px =  e*x/_tmp;
                double py =  e*y/_tmp;
                double pz =  e*z/_tmp;
                hcalsum_raw=hcalsum_raw+e;
                PseudoJet pj(px, py, pz, e);
                //double eta_r=pj.pseudorapidity();
                //double phi_r=pj.phi();
                //double pt_r=pj.pt();
                //cout << " e=" << e <<  " phi=" << pj.phi() << " eta=" << pj.eta() << endl;
                avec_hits_raw.push_back(pj);
                avec_hittime_raw.push_back(avt);

                // fill hits
                LParticle p(px, py, pz, e, layer);
                p.SetType(1); // HCAL 
                p.SetCharge(layer);
                p.SetStatus(mcp->getNMCContributions());
                p.SetParameter(x);
                p.SetParameter(y);
                p.SetParameter(z);
                p.SetParameter(layer_pos_cm);

                // find fastest hit
                float timeCont = mcp->getTimeCont(0);
                EVENT::MCParticle* pmm =mcp->getParticleCont(0);
                int pdg=pmm->getPDG();
                int status=pmm->getSimulatorStatus();
                float rawTime = timeCont;
                int nCont=mcp->getNMCContributions();
                for (int jjj=0; jjj<nCont; jjj++) {
                    if (mcp->getTimeCont(jjj) < rawTime)
                        rawTime  = mcp->getTimeCont(jjj);
                    EVENT::MCParticle* pmm =mcp->getParticleCont(jjj);
                    pdg=pmm->getPDG();
                    status=pmm->getSimulatorStatus();
                }

                p.SetParameter(rawTime); // fastest hit 
                p.SetParameter(avt);     // average hit time  
                p.SetParameter((double)pdg);
                p.SetParameter((double)status);


                /*
                     // PDG of first constribution
                     if (mcp->getNMCContributions()>0){
                         EVENT::MCParticle* pmm =mcp->getParticleCont(0);
                         int pdg=pmm->getPDG ();
                         int status=pmm->getSimulatorStatus ();
                         p.SetParameter( (double)pdg  );
                         p.SetParameter( (double)status  );
                         // p.SetParameter( (double)(mcp->getGeneratorStatus()));
                     }
                */


                simhits.push_back(p);

                // cuts as in the default reconstruction
                if (e>0.0005) h_hits_time_abovecut->Fill(Thit, e);

                // corrected by sampling fraction 
                double HCAL_SF=0.031;
                e=e/HCAL_SF;
                px =  e*x/_tmp;
                py =  e*y/_tmp;
                pz =  e*z/_tmp;
                PseudoJet pj_sf(px, py, pz, e);


            } // end fill of hits



            double ecalsum_raw=0;
            // ECAL hits
            IMPL::LCCollectionVec* col53 = (IMPL::LCCollectionVec*) evt->getCollection("EcalBarrelHits");
            nCL = col53->getNumberOfElements();
            for (int i=0; i<nCL; ++i) {
                EVENT::SimCalorimeterHit* mcp =  (EVENT::SimCalorimeterHit*) col53->getElementAt(i);
                // EVENT::CalorimeterHit* mcp =  (EVENT::CalorimeterHit*) col53->getElementAt(i) ;

                const float* pos= mcp->getPosition();
                float x=pos[0];
                float y=pos[1];
                float z=pos[2];
                double e = mcp->getEnergy();
                double _tmp = std::sqrt(x*x + y*y + z*z);
                double px =  e*x/_tmp;
                double py =  e*y/_tmp;
                double pz =  e*z/_tmp;


                // Get the two 32-bit chunks of the ID.
                int cellId0 = mcp->getCellID0();
                int cellId1 = mcp->getCellID1();
                // Make a 64-bit id for the IDDecoder.  The type MUST be "long long" and not "long".  (from Tony Johnson)
                long long cellId = ((long long)cellId1) << 32 | cellId0;
                int layer = decoder_ecal->getFieldValue("layer", cellId);
                // 1st layer on middle
                double layer_pos_cm=0.1*(layer_size_ecal_mm*0.5+(layer*layer_size_ecal_mm));
                double Thit=mcp->getTimeCont(0);


                // number of MC contributions to the hit
                // calculate average time  in [ns] 
                double avt = 0; double ave=0;
                for (int jj=0; jj<mcp->getNMCContributions(); jj++) {
                    avt=avt+mcp->getEnergyCont(jj)*mcp->getTimeCont(jj);
                    ave=ave+mcp->getEnergyCont(jj);
                }
                avt=avt/ave;

                ecalsum_raw=ecalsum_raw+e;

                PseudoJet pj(px, py, pz, e);
                double eta_r=pj.pseudorapidity();
                double phi_r=pj.phi();
                double pt_r=pj.pt();
                //cout << " e=" << e <<  " phi=" << pj.phi() << " eta=" << pj.eta() << endl;
                avec_hits_raw.push_back(pj);


                // fill hits
                LParticle p(px, py, pz, e, layer);
                p.SetCharge(layer);
                p.SetType(2); // ECAL 
                p.SetStatus(mcp->getNMCContributions());
                p.SetParameter(x);
                p.SetParameter(y);
                p.SetParameter(z);
                p.SetParameter(layer_pos_cm);

                // find fastest hit
                float timeCont = mcp->getTimeCont(0);
                EVENT::MCParticle* pmm =mcp->getParticleCont(0);
                int pdg=pmm->getPDG();
                int status=pmm->getSimulatorStatus();
                float rawTime = timeCont;
                int nCont=mcp->getNMCContributions();
                for (int jjj=0; jjj<nCont; jjj++) {
                    if (mcp->getTimeCont(jjj) < rawTime)
                        rawTime  = mcp->getTimeCont(jjj);
                    EVENT::MCParticle* pmm =mcp->getParticleCont(jjj);
                    pdg=pmm->getPDG();
                    status=pmm->getSimulatorStatus();
                }
                p.SetParameter(rawTime); // fastest hit 
                p.SetParameter(avt);     // average hit time  
                p.SetParameter((double)pdg);
                p.SetParameter((double)status);

                /*
                // PDG of first constribution
                     if (mcp->getNMCContributions()>0){
                         EVENT::MCParticle* pmm=mcp->getParticleCont(0);
                         int pdg=pmm->getPDG ();
                         int status=pmm->getSimulatorStatus ();
                         p.SetParameter( pdg  );
                         p.SetParameter( (double)status  );
                         //p.SetParameter( (double)(mcp->getGeneratorStatus()));
                     }
                */


                simhits.push_back(p);


                // correct by SF (1st, 2nd, 3rd layer are 1., 0.0184, 0.0092)
                double ECAL_SF=0.0184;
                e=e/ECAL_SF;
                px =  e*x/_tmp;
                py =  e*y/_tmp;
                pz =  e*z/_tmp;
                PseudoJet pj_sf(px, py, pz, e);
                avec_hits_raw_sf.push_back(pj_sf);



            }



            // find center of truth jet in terms of X,Y,Z
            // use EM hits
            vector<LParticle> truthjets_formatching;
            for (unsigned int j1=0; j1<truthjets.size(); j1++) {
                LParticle p1=(LParticle)truthjets.at(j1);
                TLorentzVector L1= p1.GetP();
                double pt_t =  L1.Perp();
                double phi_t =  L1.Phi();
                double eta_t =  L1.PseudoRapidity();
                double e_t =  L1.E();
                // find jet center in terms of X,Y,Z
                double Xcenter_ecal=0;
                double Ycenter_ecal=0;
                double Zcenter_ecal=0;

                double Xcenter_hcal=0;
                double Ycenter_hcal=0;
                double Zcenter_hcal=0;

                double dMin_ecal=100000;
                double dMin_hcal=100000;
                for (unsigned int j2=0; j2<simhits.size(); j2++) {
                    LParticle hit=simhits.at(j2);
                    TLorentzVector LE=hit.GetP();
                    int type=hit.GetType();
                    double phi_h=LE.Phi();
                    double eta_h=LE.PseudoRapidity();
                    double dphi=phi_h-phi_t;
                    if (abs(dphi)>kPI) dphi=k2PI-abs(dphi);
                    double deta=eta_h-eta_t;
                    double delta=sqrt(dphi*dphi+deta*deta); // distance parameter 

                   // HCAL
                    if (type==1) {
                        if (delta<dMin_hcal) {
                            dMin_hcal=delta;
                            vector<double> parh=hit.GetParameters();
                            Xcenter_hcal=parh[0];
                            Ycenter_hcal=parh[1];
                            Zcenter_hcal=parh[2];
                        }
                    }

                    // ECAL 
                    if (type==2) {
                        if (delta<dMin_ecal) {
                            dMin_ecal=delta;
                            vector<double> parh=hit.GetParameters();
                            Xcenter_ecal=parh[0];
                            Ycenter_ecal=parh[1];
                            Zcenter_ecal=parh[2];
                        }
                    }

                } // end loop 

                // rebuild truth jets for matching with hits
                LParticle p(L1.Px(), L1.Py(), L1.Pz(), L1.E(), 0);
                p.SetParameter(Xcenter_hcal); //0 
                p.SetParameter(Ycenter_hcal); //1 
                p.SetParameter(Zcenter_hcal); //2 
                // position as found in ECAL (more precise)
                p.SetParameter(Xcenter_ecal); //3 
                p.SetParameter(Ycenter_ecal); //4 
                p.SetParameter(Zcenter_ecal); //5 

                truthjets_formatching.push_back(p);

            }


            //    cout << "  new event " << endl;

            // associate hits with jets taking into account jet centers
            for (unsigned int j1=0; j1<simhits.size(); j1++) {
                LParticle hit=simhits.at(j1);
                TLorentzVector LE=hit.GetP();
                double e_h=LE.E();
                double phi_h=LE.Phi();
                double eta_h=LE.PseudoRapidity();
                vector<double> par=hit.GetParameters();
                int type= hit.GetType(); // ECAL or HCAL 
                int layer=hit.GetCharge();
                double x=par[0];
                double y=par[1];
                double z=par[2];
                double layer_pos_cm=par[3];
                double Thit=par[4];
                double LogTime=TMath::Log10(Thit);
                double avt=par[5];
                int    pdg=int(par[6]);
                int    stat=int(par[7]);
                // int    genstat=int(par[8]);


              // associate hits with truth jets 
                for (unsigned int j2=0; j2<truthjets_formatching.size(); j2++) {
                    LParticle p1=(LParticle)truthjets_formatching.at(j2);
                    TLorentzVector L1= p1.GetP();
                    double pt_t =  L1.Perp();
                    double phi_t = L1.Phi();
                    double eta_t = L1.PseudoRapidity();
                    double e_t =  L1.E();
                    vector<double> par1=p1.GetParameters();
                    double dphi=phi_h-phi_t;
                    if (abs(dphi)>kPI) dphi=k2PI-abs(dphi);
                    double deta=eta_h-eta_t;
                    double delta=sqrt(dphi*dphi+deta*deta); // distance parameter 

                    if (type==1 && Thit<1000 && delta<Rparam) { // HCAL

                    //use ECAL postion as most precise 
                        double Xcenter=par1[3];
                        double Ycenter=par1[4];
                        double Zcenter=par1[5];
                        double xhit=0.1*(x-Xcenter); // in cm 
                        double yhit=0.1*(y-Ycenter); // in cm 
                        double zhit=0.1*(z-Zcenter); // in cm 

                        // http://lcio.desy.de/v01-10/doc/doxygen_api/html/classEVENT_1_1MCParticle.html#
                        if (Thit>300) {
                            h_jet_pdg_hit300->Fill(pdg, e_h);
                            // cout << "pdg=" << pdg << " time=" << Thit << " ns" << " status=" << stat << endl;
                        }


                        // weigted energy
                        XEnergy=XEnergy+e_h;
                        XTime = XTime + Thit*e_h;

                        h_jet_energy_hit->Fill(TMath::Log10(e_h)); // hit energy 

                        // for each event
                        if (hist_ev<nXevents) h_jet_hitsjetXY_EV[hist_ev]->Fill(xhit, yhit, Thit);
                        // time for each layer
                        if (layer<nLayersHCAL) h_jet_time_layerHCAL[layer]->Fill(Thit, e_h);

                        //cout  << " x ="<< xhit << " y=" << yhit << endl;
                        // as for slicPandora, look at first time contribution
                        h_jet_hitstime_log->Fill(LogTime, e_h);
                        h_jet_hitstime->Fill(Thit, e_h);
                        h_jet_hitstime2D->Fill(LogTime, TMath::Log10(e_h), e_h);
                        h_jet_hitstime_prof->Fill(Thit, e_h);
                        h_jet_hitstime_prof_log->Fill(LogTime, e_h);

                        double dtrans_cm=sqrt(xhit*xhit+yhit*yhit);
                        h_jet_hitsRLE->Fill(dtrans_cm, layer_pos_cm, e_h);
                        h_jet_hitsjetXY->Fill(xhit, yhit, e_h);
                        if (delta<Rparam) {
                            h_jet_hitsjetXY_jet->Fill(xhit, yhit, e_h);
                        }
                        h_jet_hitsjet_Trans->Fill(dtrans_cm, e_h);
                        h_jet_hitsjet_Depth->Fill(layer_pos_cm, e_h);

                        h_jet_hitspos_prof->Fill(dtrans_cm, Thit, e_h);
                        h_jet_ehitspos_prof->Fill(dtrans_cm, e_h);

                        h_jet_hitlayer_prof->Fill((double)layer, Thit, e_h);
                        h_jet_hitdist_prof->Fill(layer_pos_cm, Thit, e_h);
                        h_jet_ehitdist_prof->Fill(layer_pos_cm, e_h);

                        h_jet_hitlayer_hcal_prof->Fill((double)layer, Thit, e_h);

                        h_jet_hitsRLT->Fill(dtrans_cm, layer_pos_cm, Thit);
                        h_jet_hitsjetXY_prof1->Fill(xhit, yhit, e_h);
                        h_jet_hitsjetXY_prof2->Fill(xhit, yhit, Thit);

                        h_jet_avhitstime2D->Fill(TMath::Log10(avt), TMath::Log10(e_h), e_h);
                        h_jet_avhitstime->Fill(TMath::Log10(avt), e_h);
                        h_jet_hits_energy_frac->Fill(TMath::Log10(e_h), e_h/e_t);
                        h_jet_hits_energytime_frac->Fill(LogTime, e_h/e_t);
                    } // hcal 

  /// ECAL

                    if (type==2 && Thit<1000 && delta<Rparam) {  // ECAL

                        // ECAL
                        double Xcenter=par1[3];
                        double Ycenter=par1[4];
                        double Zcenter=par1[5];
                        double xhit=0.1*(x-Xcenter); // in cm 
                        double yhit=0.1*(y-Ycenter); // in cm 
                        double zhit=0.1*(z-Zcenter); // in cm 
                        double dtrans_cm=sqrt(xhit*xhit+yhit*yhit);

                        // for each event
                        if (hist_ev<nXevents) h_jet_hitsjetXY_EV[hist_ev]->Fill(xhit, yhit, Thit);
                        if (layer<nLayersECAL) h_jet_time_layerECAL[layer]->Fill(Thit, e_h);

                        h_jet_hitspos_ecal_prof->Fill(dtrans_cm, Thit, e_h);
                        h_jet_hitlayer_ecal_prof->Fill((double)layer, Thit, e_h);
                        h_jet_hitsjetXY_ECAL->Fill(xhit, yhit, e_h);
                        h_jet_hitsjetXY_ECAL_prof2->Fill(xhit, yhit, Thit);
                        h_jet_hitstime2D_ECAL->Fill(LogTime, TMath::Log10(e_h), e_h);
                    }


                }


            } // close loop over  hits



            hist_ev++;

            // HCAL hits after created by slicPandora 
            double hcalsum=0;

            vector<PseudoJet> avec_hits;
            IMPL::LCCollectionVec* col51 = (IMPL::LCCollectionVec*) evt->getCollection("HAD_BARREL");
            nCL = col51->getNumberOfElements();
            for (int i=0; i<nCL; ++i) {
                // EVENT::SimCalorimeterHit* mcp =  (EVENT::SimCalorimeterHit*) col51->getElementAt(i) ;
                EVENT::CalorimeterHit* mcp =  (EVENT::CalorimeterHit*) col51->getElementAt(i);

                const float* pos= mcp->getPosition();
                float x=pos[0];
                float y=pos[1];
                float z=pos[2];
                double e = mcp->getEnergy();
                double _tmp = std::sqrt(x*x + y*y + z*z);
                double px =  e*x/_tmp;
                double py =  e*y/_tmp;
                double pz =  e*z/_tmp;

                hcalsum=hcalsum+e;

                //cout << e << endl;

               // alternative
               // TVector3 caloposition(x,y,z);
               // double curPhi = caloposition.Phi();
               // double curEta = caloposition.Eta();
               // double curPt = sin(caloposition.Theta())*e;
               // TLorentzVector cp4;
               // cp4.SetPtEtaPhiE(curPt,curEta,curPhi,e);


                //double theta=mcp->getITheta();
                //double phi=mcp->getIPhi();
                //double eta=-log(tan(0.5*theta));
                //double et=e*sin(theta);

                //if (e<0.1) continue; // min energy
                //double pz=e*cos(theta);
                //double px=et*cos(theta);
                //double py=et*sin(theta);
                PseudoJet pj(px, py, pz, e);
                double eta_r=pj.pseudorapidity();
                double phi_r=pj.phi();
                double pt_r=pj.pt();
                //cout << " e=" << e <<  " phi=" << pj.phi() << " eta=" << pj.eta() << endl;
                avec_hits.push_back(pj);
            }


            //cout << "HCal raw sum=" << hcalsum_raw << endl;
            //cout << "HCal sum after SF=" << hcalsum << endl;



            double ecalsum=0;
            // ECAL hits
            IMPL::LCCollectionVec* col52 = (IMPL::LCCollectionVec*) evt->getCollection("EM_BARREL");
            nCL = col52->getNumberOfElements();
            for (int i=0; i<nCL; ++i) {
                // EVENT::SimCalorimeterHit* mcp =  (EVENT::SimCalorimeterHit*) col52->getElementAt(i) ;
                EVENT::CalorimeterHit* mcp =  (EVENT::CalorimeterHit*) col52->getElementAt(i);

                const float* pos= mcp->getPosition();
                float x=pos[0];
                float y=pos[1];
                float z=pos[2];
                double e = mcp->getEnergy();
                double _tmp = std::sqrt(x*x + y*y + z*z);
                double px =  e*x/_tmp;
                double py =  e*y/_tmp;
                double pz =  e*z/_tmp;


                ecalsum=ecalsum+e;

                //double theta=mcp->getITheta();
                //double phi=mcp->getIPhi();
                //double eta=-log(tan(0.5*theta));
                //double et=e*sin(theta);

                //if (e<0.1) continue; // min energy
                //double pz=e*cos(theta);
                //double px=et*cos(theta);
                //double py=et*sin(theta);
                PseudoJet pj(px, py, pz, e);
                double eta_r=pj.pseudorapidity();
                double phi_r=pj.phi();
                double pt_r=pj.pt();
                //cout << " e=" << e <<  " phi=" << pj.phi() << " eta=" << pj.eta() << endl;
                avec_hits.push_back(pj);
            }





            //cout << "ECal raw hits =" << ecalsum_raw << endl;
            //cout << "ECal sum after SF=" << ecalsum << endl;


           // ----------------- cluster jets --------------------------
            ClusterSequence clust_seq_clus(avec_clus, jet_def);
            vector<PseudoJet> jets_clus = clust_seq_clus.inclusive_jets(0.8*ETmin);
            vector<PseudoJet> sjets_clus = sorted_by_pt(jets_clus);
            vector<LParticle> clusjets;
            nn=0;
            for (unsigned int k = 0; k<sjets_clus.size(); k++) {
                double eta=sjets_clus[k].pseudorapidity();
                double phi=sjets_clus[k].phi();
                if (phi<0)  phi = phi + k2PI;
                double m=jets_clus[k].m();
                double pt = sjets_clus[k].perp();
                double e = sjets_clus[k].e();
                // fill jets 
                h_e_jet->Fill(e);
                h_pt_jet->Fill(pt);
                h_eta_jet->Fill(eta);
                if (pt < ETmin)                    continue;
                if (fabs(eta)> ETAmax)            continue;
                LParticle p(sjets_clus[k].px(), sjets_clus[k].py(), sjets_clus[k].pz(), sjets_clus[k].e(), 0);


                // energy of hits created by slicPandora 
                double hitsum=0;
                for (unsigned int j4=0; j4<avec_hits.size(); j4++) {
                    PseudoJet p=(PseudoJet)avec_hits.at(j4);
                    double pt_h =  p.perp();
                    double eta_h = p.eta();
                    double phi_h = p.phi();
                    double dphi=phi-phi_h;
                    if (abs(dphi)>kPI) dphi=k2PI-abs(dphi);
                    double deta=eta-eta_h;
                    double delta=sqrt(dphi*dphi+deta*deta); // distance parameter 
                    if (delta<Rparam) hitsum=hitsum+pt_h;
                }


                // energy of raw hits before slicPandora 
                double hitsum_raw=0;
                for (unsigned int j4=0; j4<avec_hits_raw.size(); j4++) {
                    PseudoJet p=(PseudoJet)avec_hits_raw.at(j4);
                    double time=avec_hittime_raw[j4];
                    double pt_h =  p.perp();
                    double eta_h = p.eta();
                    double phi_h = p.phi();
                    double dphi=phi-phi_h;
                    if (abs(dphi)>kPI) dphi=k2PI-abs(dphi);
                    double deta=eta-eta_h;
                    double delta=sqrt(dphi*dphi+deta*deta); // distance parameter 
                    if (delta<Rparam) {
                        double ee=p.e();
                        if (time>0 && p.e()>0) {
                            //h_jet_avhitstime2D->Fill(log(time), -1*log(ee), ee);
                            //h_jet_avhitstime->Fill(log(time),  ee);
                        }
                        hitsum_raw=hitsum_raw+pt_h;
                    }
                }


                // energy of raw hits corrected by SF 
                double hitsum_raw_sf=0;
                for (unsigned int j4=0; j4<avec_hits_raw_sf.size(); j4++) {
                    PseudoJet p=(PseudoJet)avec_hits_raw_sf.at(j4);
                    double pt_h =  p.perp();
                    double eta_h = p.eta();
                    double phi_h = p.phi();
                    double dphi=phi-phi_h;
                    if (abs(dphi)>kPI) dphi=k2PI-abs(dphi);
                    double deta=eta-eta_h;
                    double delta=sqrt(dphi*dphi+deta*deta); // distance parameter 
                    if (delta<Rparam) hitsum_raw_sf=hitsum_raw_sf+pt_h;
                }


                // fill jet substructure
                p.SetParameter(EffectiveRadius(sjets_clus[k], sjets_clus[k].constituents(), Rparam)); // 0 
                p.SetParameter(nsubjettiness(sjets_clus[k], sjets_clus[k].constituents(), 1, Rparam)); // 1 
                p.SetParameter(nsubjettiness(sjets_clus[k], sjets_clus[k].constituents(), 2, Rparam)); // 2 
                p.SetParameter(nsubjettiness(sjets_clus[k], sjets_clus[k].constituents(), 3, Rparam)); //  3 
                p.SetParameter(splittingscale(sjets_clus[k])); // 4 
                p.SetParameter(eccentricity(sjets_clus[k], sjets_clus[k].constituents())); // 5
                p.SetParameter(hitsum); // 6 
                p.SetParameter(hitsum_raw); // 7 
                p.SetParameter(hitsum_raw_sf); // 8 

                // number of clusters in leading jet
                if (k==0) {
                    h_jet_n_clusters->Fill(sjets_clus[k].constituents().size());
                    vector<PseudoJet> constituents=sjets_clus[k].constituents();
                    unsigned int size=constituents.size();
                    h_jet_n_clusters->Fill(double(size));
                    for (unsigned int i =0; i < size; i++) {
                        double et=constituents[i].Et();
                        h_jet_pt_clusters->Fill(et);
                        cout <<"jet_pt_clusters ="<<et<<endl;
                        
                    }
                } // end leading jet 



                clusjets.push_back(p);


                //MB Reco Jets
                vector<PseudoJet> constit=sjets_clus[k].constituents();
                unsigned int ccsize=constit.size();
                for (unsigned int i=0; i<ccsize; i++) {
                    // std::cout << "Clus Jets const.Et(): " << (constits[i].Et()) << std::endl;
                    h_jet_econst_clus_frac->Fill(TMath::Log10(constit[i].e()), constit[i].e()/e);
                    h_reco_jets_const_Et->Fill(constit[i].Et());
                }
                if (pt >= 10000) {
                    for (unsigned int i=0; i<ccsize; i++) {
                        // std::cout << "Clus Jets const.Et(): " << (constits[i].Et()) << std::endl;
                        h_reco_jets_const_Et10->Fill(constit[i].Et());
                    }
                }


                nn++;
                if (nn>2) break; // take first 2 jets
            }


            // fill jet substructure first
            // intrested in 2 leading jets only!
            for (unsigned int j=0; j<clusjets.size(); j++) {
                LParticle p=(LParticle)clusjets.at(j);
                TLorentzVector L= p.GetP();
                double pt =  L.Perp();
                double eta =  L.Eta();
                double mass =  L.M();
                h_jet_pt_clus->Fill(pt);
                cout <<"jet_pt_clus ="<<pt<<endl;
                h_jet_m_clus->Fill(mass);
                cout<<"jet_m_clus ="<<mass<<endl;
                vector<double> par1=p.GetParameters();
                double jet1_tau32=par1[3]/par1[2];
                double jet1_tau21=par1[2]/par1[1];
                double jet1_d12=par1[4];
                double jet1_effR_cut=par1[0];
                float ecc1=par1[5];    // eccentricity
                h_jet_eccent1->Fill(ecc1);
                h_effR_j1->Fill(jet1_effR_cut);
                h_tau21_j1->Fill(jet1_tau21);
                h_tau32_j1->Fill(jet1_tau32);
                h_d12_j1->Fill(jet1_d12);
                if (j>1) break; // take 2 jets only 
            }

            // make mass
            if (clusjets.size() >1) {
                // cout << "Nr of clus jets=" << clusjets.size() << endl;
                LParticle L1=(LParticle)clusjets.at(0);
                LParticle L2=(LParticle)clusjets.at(1);
                TLorentzVector LL=L1.GetP()+L2.GetP();
                h_jetjet_m_clus->Fill(LL.M());

            }



            // jet resolution
            for (unsigned int j1=0; j1<truthjets.size(); j1++) {
                LParticle p1=(LParticle)truthjets.at(j1);
                TLorentzVector L1= p1.GetP();
                double pt_t =  L1.Perp();
                double phi_t =  L1.Phi();
                double eta_t =  L1.Eta();
                double e_t =  L1.E();

                // intrested in 2 leading jets only!
                double pt_matched=-1;
                double pt_matched_hits=0;
                double pt_matched_hits_raw=0;
                double pt_matched_hits_raw_sf=0;


                for (unsigned int j2=0; j2<clusjets.size(); j2++) {
                    LParticle p2=(LParticle)clusjets.at(j2);
                    TLorentzVector L2= p2.GetP();
                    vector<double> par1=p2.GetParameters();
                    double hitsum=par1[6];
                    double hitsum_raw=par1[7];
                    double hitsum_raw_sf=par1[8];

                    double pt_r =  L2.Perp();
                    double phi_r =  L2.Phi();
                    double eta_r =  L2.Eta();
                    double e_r =  L2.E();
                    double dphi=phi_t-phi_r;
                    if (abs(dphi)>kPI) dphi=k2PI-abs(dphi);
                    double deta=eta_t-eta_r;
                    double delta=sqrt(dphi*dphi+deta*deta); // distance parameter 
                    if (delta<0.2) {
                        pt_matched=1.17*pt_r; // correction x17% 
                        pt_matched_hits=1.17*hitsum;
                        pt_matched_hits_raw=45*hitsum_raw; // correction x40 
                        pt_matched_hits_raw_sf=1.17*hitsum_raw_sf; // SF corrected hits 
                    }
                }



                // if (pt_matched>0) cout << pt_matched/pt_t << endl;

                if (pt_matched>0 && pt_t>0) {
                    for (int kk=0; kk<nmax; kk++) {
                        double x1=pow(2, kk+3);
                        double x2=pow(2, kk+3+1);
                        if (pt_t>x1 && pt_t<x2) {
                            //cout << " Rjets=" << pt_matched/pt_t << " hits=" << pt_matched_hits/pt_t << " hits=" << pt_matched_hits_raw/pt_t << endl;
                            h_jet_res[kk]->Fill(pt_matched/pt_t); h_jet_res_hits[kk]->Fill(pt_matched_hits/pt_t); h_jet_res_hits_raw[kk]->Fill(pt_matched_hits_raw/pt_t);
                            h_jet_res_hits_raw_sf[kk]->Fill(pt_matched_hits_raw_sf/pt_t);

                            h_jet_ptr[kk]->Fill(pt_t);  h_jet_ptr_hits[kk]->Fill(pt_t); h_jet_ptr_hits_raw[kk]->Fill(pt_t);
                            h_jet_ptr_hits_raw_sf[kk]->Fill(pt_t);

                        }
                    }
                }


            } // end calo loop





          // look at track resolution

            if (mtype==2) {
                // look at reconstructed tracks using Helix
                double _bField=5;
                // Reconstructed tracks
                // look up at: /share/sl6/ilcsoft/slic/release-v05-00-00/slicPandora/HEAD/lcio/v02-04-03/build/include/EVENT
                vector<PseudoJet> avec_tracks;
                IMPL::LCCollectionVec* colT = (IMPL::LCCollectionVec*) evt->getCollection("Tracks");
                unsigned int  nTracks = colT->getNumberOfElements();
                for (unsigned int i=0; i<nTracks; ++i) {
                    EVENT::Track* track =  (EVENT::Track*) colT->getElementAt(i);
                    float d0 = track->getD0();
                    float z0 = track->getZ0();
                    float omega = track->getOmega();
                    float tanLambda = track->getTanLambda();
                    float phi0   = track->getPhi();
                    float radius =1.0/omega;
                    float x0 = radius*cos(phi0-k2PI);
                    float y0 = radius*sin(phi0-k2PI);
                    const pandora::Helix helixFit(phi0, d0, z0, omega, tanLambda, _bField);
                    const float recoMomentum(helixFit.GetMomentum().GetMagnitude());
                    double px=helixFit.GetMomentum().GetX();
                    double py=helixFit.GetMomentum().GetY();
                    double pz=helixFit.GetMomentum().GetZ();
                    double m = 0; // mcp->getMomentum()[3];
                    double e=sqrt(px*px+py*py+pz*pz+m*m);
                    PseudoJet pp(px, py, pz, e);
                    double eta_r=pp.pseudorapidity();
                    double phi_r=pp.phi();
                    double pt_r=pp.pt();
                    h_pt_track->Fill(pt_r);
                    h_eta_track->Fill(eta_r);


                    // match reconstructed track with truth-level track
                    double pt_t=-1;
                    for (unsigned int j=0; j<avec_truth.size(); j++) {
                        PseudoJet ptrue=avec_truth[j];
                        double dphi=phi_r-ptrue.phi();
                        if (abs(dphi)>kPI) dphi=k2PI-abs(dphi);
                        double deta=eta_r-ptrue.pseudorapidity();
                        double delta=sqrt(dphi*dphi+deta*deta); // distance parameter 
                        double r=0;
                        if (delta<0.1) pt_t=ptrue.pt();
                    } // end matching

                    if (pt_t>0) {
                        for (int kk=0; kk<nmax; kk++) {
                            double x1=pow(2, kk+3);
                            double x2=pow(2, kk+3+1);
                            if (pt_t>x1 && pt_t<x2) {
                                h_track_res[kk]->Fill(pt_r/pt_t); h_track_ptr[kk]->Fill(pt_t);
                            }
                        }
                    }

                } // end track resolution 
            } // end single particle track resolution







        } // end loop 



        lcReader->close();
        delete lcReader;

    } // close the file 

    //m_ntuple->Fill();
    RootFile->Write();
    //RootFile->Print();
    RootFile->Close();

    cout << "Total hit energy in HCAL for antiKT5=" << XEnergy << endl;
    cout << "Total time*energy in HCAL for antiKT5 =" << XTime << endl;
    cout << "Weighted Total time in HCAL [ns] =" << XTime/XEnergy << endl;
    
    
    
    
    


    cout << "Writing ROOT file "+ outputfile << endl;

    return 0;
}

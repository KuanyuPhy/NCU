/***************************************************************************
 *  How to use SLCIO files from HepSim, and how to build anti-KT jets 
 *  S.Chekanov (ANL) chekanov@anl.gov
 *  A library for HEP events storage and processing based on Google's PB   
 *  The project web site: http://atlaswww.hep.anl.gov/hepsim/
****************************************************************************/

#include <iostream>
#include <fstream>
#include <stdlib.h>
#include <cmath>
#include <math.h>
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

#include "time.h"
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

const double kPI = TMath::Pi();
const double k2PI = 2 * kPI;
#include "fastjet/PseudoJet.hh"
#include "fastjet/ClusterSequence.hh"
using namespace fastjet;

#include <fastjet/ClusterSequence.hh>
#include <fastjet/GhostedAreaSpec.hh>
#include <fastjet/ClusterSequenceArea.hh>
#include "fastjet/tools/Filter.hh"
#include "fastjet/tools/Pruner.hh"
#include "fastjet/tools/MassDropTagger.hh"
#include "fastjet/GhostedAreaSpec.hh"
#include "fastjet/PseudoJet.hh"
#include "fastjet/JetDefinition.hh"

//#ifdef __MAKECINT__
////#pragma link C++ class vector<float>+;
////#endif
//
//using namespace fastjet::contrib;
//

float EffectiveRadius(PseudoJet Jet, vector<PseudoJet> constituents, double jetR = 0.5)
{
  float Energy = Jet.Et();
  float numerator = 0;
  int size = constituents.size();
  for (int i = 0; i < size; i++)
  {
    if (Jet.delta_R(constituents[i]) > jetR)
      continue;
    numerator += constituents[i].Et() * Jet.delta_R(constituents[i]);
  }
  //cout << Energy << endl;
  //cout << numerator << endl;
  return numerator / Energy;
}

float eccentricity(PseudoJet Jet, vector<PseudoJet> constituents)
{
  unsigned int num = constituents.size();
  double Dphi[num], Deta[num], E[num];
  double etaSum = 0.;
  double phiSum = 0.;
  double eTot = 0.;

  for (unsigned int j = 0; j < num; j++)
  {
    PseudoJet cp = constituents.at(j);
    E[j] = cp.e();
    Dphi[j] = Jet.phi() - cp.phi();
    // if (Dphi[j]>TMath::Pi()) Dphi[j]=2*TMath::Pi()-Dphi[j];
    if (fabs(Dphi[j] - 2. * TMath::Pi()) < fabs(Dphi[j]))
      Dphi[j] -= 2. * TMath::Pi();
    if (fabs(Dphi[j] + 2. * TMath::Pi()) < fabs(Dphi[j]))
      Dphi[j] += 2. * TMath::Pi();
    Deta[j] = Jet.eta() - cp.eta();
    etaSum = etaSum + Deta[j] * E[j];
    phiSum = phiSum + Dphi[j] * E[j];
    eTot = eTot + E[j];
  }

  etaSum = etaSum / eTot;
  phiSum = phiSum / eTot;
  for (unsigned int j = 0; j < num; j++)
  {
    Deta[j] = Deta[j] - etaSum;
    Dphi[j] = Dphi[j] - phiSum;
  }

  double X1 = 0.;
  double X2 = 0;
  for (unsigned int i = 0; i < num; i++)
  {
    X1 += 2. * E[i] * Deta[i] * Dphi[i];
    X2 += E[i] * (Dphi[i] * Dphi[i] - Deta[i] * Deta[i]);
  }

  // variance calculations
  double Theta = .5 * atan(X1 / X2);
  double sinTheta = TMath::Sin(Theta);
  double cosTheta = TMath::Cos(Theta);
  double Theta2 = Theta + 0.5 * TMath::Pi();
  double sinThetaPrime = TMath::Sin(Theta2);
  double cosThetaPrime = TMath::Cos(Theta2);

  double VarX = 0.;
  double VarY = 0.;
  for (unsigned int i = 0; i < num; i++)
  {
    double X = cosTheta * Deta[i] - sinTheta * Dphi[i];
    double Y = sinTheta * Deta[i] + cosTheta * Dphi[i];
    VarX += E[i] * X * X;
    VarY += E[i] * Y * Y;
  }

  double VarianceMax = VarX;
  double VarianceMin = VarY;
  if (VarianceMax < VarianceMin)
  {
    VarianceMax = VarY;
    VarianceMin = VarX;
  }

  double ECC = 1.0 - (VarianceMin / VarianceMax);

  return ECC;
}

double nsubjettiness(PseudoJet Jet, vector<PseudoJet> constituents, int NSubJets, double jetRad = 0.5)
{

  //vector<CParticle> constit = jet.GetConstituents();
  vector<PseudoJet> jetConstit;

  unsigned int num = constituents.size();

  if (num < (unsigned int)NSubJets)
  {
    return -999;
  }
  TLorentzVector Jet_p;
  Jet_p.SetPxPyPzE(Jet.px(), Jet.py(), Jet.pz(), Jet.E());
  num = 0;
  for (unsigned int i = 0; i < constituents.size(); i++)
  {
    PseudoJet c_i = constituents[i];
    if (c_i.delta_R(Jet_p) > jetRad)
      continue;
    jetConstit.push_back(c_i);
    num++;
  }
  if (num < (unsigned int)NSubJets)
  {
    return -999;
  }
  std::vector<std::vector<fastjet::PseudoJet>> kt_subjets_vec; //a vector of vectors of Pseudojets
  fastjet::JetDefinition *m_jetdef = new fastjet::JetDefinition(fastjet::kt_algorithm, 1.5, fastjet::E_scheme, fastjet::Best);
  fastjet::ClusterSequence kt_seq(jetConstit, *m_jetdef);
  delete m_jetdef;

  for (unsigned int i = 0; i < (unsigned int)NSubJets; i++)
  {
    kt_subjets_vec.push_back(fastjet::sorted_by_pt(kt_seq.exclusive_jets((int)NSubJets)));
  }
  double min_dist = 100000.0;
  double sum_pt = 0.0;
  double sum_dist = 0.0;
  //first find the minimum distance.
  for (unsigned int i = 0; i < jetConstit.size(); i++)
  {
    fastjet::PseudoJet theconstit(jetConstit[i]);
    sum_pt += theconstit.perp();
    float min_dist = 1e10;
    for (unsigned int j = 0; j < (unsigned int)NSubJets; j++)
    {
      const std::vector<fastjet::PseudoJet> *kt_subjets = &(kt_subjets_vec[j]);
      float temp_dist = theconstit.perp() * std::sqrt(kt_subjets->at(j).plain\
_distance(theconstit));
      if (temp_dist < min_dist)
        min_dist = temp_dist;
    } //loop over axis (subjets)
    sum_dist += min_dist;
  } //loop over jet constituents

  sum_dist /= (jetRad * sum_pt);

  double nSubJettiness = sum_dist;
  if (sum_dist > 1.0)
    cout << "uh oh" << sum_dist << endl;

  return nSubJettiness;
}

double splittingscale(PseudoJet Jet)
{
  if (!Jet.has_constituents())
    return -5.;

  vector<PseudoJet> jetConstit = Jet.constituents();

  double dR = Jet.associated_cluster_sequence()->jet_def().R();
  fastjet::JetDefinition *m_jetdef = new fastjet::JetDefinition(fastjet::kt_algorithm, dR, fastjet::E_scheme, fastjet::Best);

  fastjet::ClusterSequence kt_seq(jetConstit, *m_jetdef);
  delete m_jetdef;
  return dR * TMath::Sqrt(kt_seq.exclusive_dmerge(1));
}

// find all files inside a directory
std::vector<std::string> open(std::string name = "data.in")
{
  vector<std::string> ntup;
  ifstream myfile;
  myfile.open(name.c_str(), ios::in);

  if (!myfile)
  {
    cerr << " -> Can't open input file:  " << name << endl;
    exit(1);
  }
  else
  {
    cout << "-> Read data file=" << name << endl;
  }

  string temp;
  while (myfile >> temp)
  {
    //the following line trims white space from the beginning of the string
    temp.erase(temp.begin(), std::find_if(temp.begin(), temp.end(), not1(ptr_fun<int, int>(isspace))));
    if (temp.find("#") == 0)
      continue;
    ntup.push_back(temp);
  }
  cout << "-> Number of files=" << ntup.size() << endl;
  myfile.close();

  for (unsigned int i = 0; i < ntup.size(); i++)
  {
    cout << ".. file to analyse=" + ntup[i] << endl;
  }
  return ntup;
}

// main example
int main(int argc, char **argv)
{

  cout << "TMath::Power(10,2)" << TMath::Power(10, 2) << endl;
  std::vector<std::string> files = open("data.in");
  int mtype = 2; // single-particles

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

  string outputfile = "root/output.root";
  cout << "\n -> Output file is =" << outputfile << endl;
  TFile *RootFile = new TFile(outputfile.c_str(), "RECREATE", "Histogram file");

  TH1D *h_debug = new TH1D("debug", "events", 10, 0, 10);

  TH1D *h_pt_jet = new TH1D("jet_pt", "pt jets", 400, 0, 1000);
  TH1D *h_e_jet = new TH1D("jet_energy", "energy jets", 5000, 0, 1000);
  TH1D *h_eta_jet = new TH1D("jet_eta", "eta jets", 120, -6, 6);
  TH1D *h_pt_clus = new TH1D("clus_pt", "pt RecoClus", 400, 0, 1000);
  TH1D *h_eta_clus = new TH1D("clus_eta", "eta RecoClus", 120, -6, 6);
  TH1D *h_pt_pfa = new TH1D("pfa_pt", "pt PFA", 400, 0, 1000);
  TH1D *h_eta_pfa = new TH1D("pfa_eta", "eta PFA", 120, -6, 6);
  TH1D *h_pt_track = new TH1D("track_pt", "pt track", 400, 0, 1000);
  TH1D *h_eta_track = new TH1D("track_eta", "eta track", 120, -6, 6);

  TH1D *h_jet_n_truth = new TH1D("jet_n_truth", "Nr of truth jets", 20, 0, 20);
  TH1D *h_jet_pt_truth = new TH1D("jet_pt_truth", "pT [GeV]", 200, 0, 50000);
  TH1D *h_jet_m_truth = new TH1D("jet_m_truth", "Mass [GeV]", 100, 0, 600);
  TH1D *h_jetjet_m_truth = new TH1D("jetjet_m_truth", "Mass(jj) [GeV]", 500, 0, 100000);
  TH1D *h_jet_econst_truth = new TH1D("econst_truth", "Const energy", 1000, 0, 500);
  TH1D *h_jet_econst_truth_sim = new TH1D("econst_truth_sim", "Const energy with Geant4 particles", 1000, 0, 500);

  // fractional energy
  TH1D *h_jet_econst_truth_frac = new TH1D("econst_truth_frac", "Fraction of Const energy", 120, -1, 5);
  TH1D *h_jet_econst_truth_sim_frac = new TH1D("econst_truth_sim_frac", "Fraction of Const energy with Geant4 particles", 120, -1, 5);
  TH1D *h_jet_pt_truth_sim = new TH1D("jet_pt_truth_sim", "pT [GeV] plus Geant4", 200, 0, 50000);

  h_jet_econst_truth_frac->GetXaxis()->SetTitle("log10 (E(truth) [GeV] )");
  h_jet_econst_truth_sim_frac->GetXaxis()->SetTitle("log10 (E (truth+geant4) [GeV] )");

  // fractional energy for clusters
  TH1D *h_jet_econst_clus_frac = new TH1D("econst_clus_frac", "Fraction of jet carried by cluster", 120, -1, 5);
  h_jet_econst_clus_frac->GetXaxis()->SetTitle("log10 (E(clusters) [GeV] )");

  TH1D *h_jet_pt_clus = new TH1D("jet_pt_clus", "pT(clus) [GeV]", 200, 0, 50000);
  TH1D *h_jet_m_clus = new TH1D("jet_m_clus", "Mass(clus) [GeV]", 100, 0, 600);
  TH1D *h_jetjet_m_clus = new TH1D("jetjet_m_clus", "Mass(jj), clusters [GeV]", 500, 0, 100000);

  TH1D *h_jet_pt_pfo = new TH1D("jet_pt_pfo", "pT(pfo) [GeV]", 200, 0, 50000);
  TH1D *h_jet_m_pfo = new TH1D("jet_m_pfo", "Mass(pfo) [GeV]", 100, 0, 600);
  TH1D *h_jetjet_m_pfo = new TH1D("jetjet_m_pfo", "Mass(jj), PFA [GeV]", 500, 0, 100000);

  // all based on clusters
  TH1D *h_jet_pt_clusters = new TH1D("jet_pt_clusters", "pT of jet clusters", 2000, 0, 10000);
  TH1D *h_jet_n_clusters = new TH1D("jet_n_clsuters", "number of clusters in jet", 200, 0, 1000);
  TH1D *h_jet_eccent1 = new TH1D("jet_eccent1", "jet1 eccent1", 40, 0, 1.1);
  TH1D *h_jet_eccent2 = new TH1D("jet_eccent2", "jet2 eccent2", 40, 0, 1.1);
  TH1D *h_effR_j1 = new TH1D("h_effR_j1", "Effective R Lead Jet", 200, 0., 1.0);
  TH1D *h_effR_j2 = new TH1D("h_effR_j2", "Effective R Sub-leading Jet", 200, 0., 1.0);
  TH1D *h_d12_j1 = new TH1D("h_d12_j1", "d_{12} Lead Jet", 40, 0., 400.);
  TH1D *h_d12_j2 = new TH1D("h_d12_j2", "d_{12} Sub-leading Jet", 40, 0., 400.);
  TH1D *h_tau21_j1 = new TH1D("h_tau21_j1", "#tau_{21} Lead Jet", 40, 0., 1.);
  TH1D *h_tau21_j2 = new TH1D("h_tau21_j2", "#tau_{21} Sub-leading Jet", 40, 0., 1.);
  TH1D *h_tau32_j1 = new TH1D("h_tau32_j1", "#tau_{32} Lead Jet", 40, 0., 1.);
  TH1D *h_tau32_j2 = new TH1D("h_tau32_j2", "#tau_{32} Sub-leading Jet", 40, 0., 1.);

  TH1D *h_true_eccent1 = new TH1D("true_eccent1", "true eccent1", 40, 0, 1.1);
  TH1D *h_true_effR_j1 = new TH1D("true_effR_j1", "Effective R Lead Jet", 400, 0., 1.0);
  TH1D *h_true_d12_j1 = new TH1D("true_d12_j1", ";d_{12} Lead Jet", 40, 0., 400.);
  TH1D *h_true_tau21_j1 = new TH1D("true_tau21_j1", ";#tau_{21} Lead Jet", 40, 0., 1.);
  TH1D *h_true_tau32_j1 = new TH1D("true_tau32_j1", ";#tau_{32} Lead Jet", 40, 0., 1.);

  // MB ET Jets
  TH1D *h_truth_jets_const_Et = new TH1D("truth_jets_cont_Et", "truth jets const Et", 2000, 0, 1000);
  TH1D *h_reco_jets_const_Et = new TH1D("reco_jets_const_Et", "reco jets const Et", 2000, 0, 1000);

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

  int hist_ev = 0;
  static const int nXevents = 20;
  TProfile2D *h_jet_hitsjetXY_EV[nXevents];
  for (Int_t j = 0; j < nXevents; j++)
  {
    h_jet_hitsjetXY_EV[j] = new TProfile2D(Form("XY_time_event_%02d", j), Form("Time of hit vs XY for event %02d", j), 160, -400.0, 400, 160, -400, 400);
    h_jet_hitsjetXY_EV[j]->GetXaxis()->SetTitle("X pos [cm]");
    h_jet_hitsjetXY_EV[j]->GetYaxis()->SetTitle("Y pos [cm]");
    h_jet_hitsjetXY_EV[j]->GetZaxis()->SetTitle("Hit time [ns]");
  }

  static const int nLayersHCAL = 64;
  static const int nLayersECAL = 40;
  double xbins[] = {0.0, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10., 12., 14., 16., 18., 20., 25, 30, 40, 60, 80, 100, 200, 400, 600, 1000};
  const int nBins = sizeof(xbins) / sizeof(double);
  TH1D *h_jet_time_layerECAL[nLayersECAL];
  TH1D *h_jet_time_layerHCAL[nLayersHCAL];
  for (Int_t j = 0; j < nLayersHCAL; j++)
  {
    h_jet_time_layerHCAL[j] = new TH1D(Form("hcal_time_layer_%02d", j), Form("HCAL Time of hit vs for layer %02d", j), nBins - 1, xbins);
    h_jet_time_layerHCAL[j]->GetXaxis()->SetTitle("Time [ns]");
    h_jet_time_layerHCAL[j]->GetYaxis()->SetTitle("Energy [GeV]");
    h_jet_time_layerHCAL[j]->Sumw2();
  }
  for (Int_t j = 0; j < nLayersECAL; j++)
  {
    //h_jet_time_layerECAL[j] = new TH1D(Form("ecal_time_layer_%02d",j), Form("ECAL Time of hit vs for layer %02d",j),nBins-1, xbins);
    h_jet_time_layerECAL[j] = new TH1D(Form("ecal_time_layer_%02d", j), Form("ECAL Time of hit vs for layer %02d", j), 200, 0, 20.);
    h_jet_time_layerECAL[j]->GetXaxis()->SetTitle("Time [ns]");
    h_jet_time_layerECAL[j]->GetYaxis()->SetTitle("Energy");
    h_jet_time_layerECAL[j]->Sumw2();
  }

  // bin sizes
  TH1D *binsT = new TH1D("bins_time", "bins_time", nBins - 1, xbins);
  binsT->Sumw2();
  for (Int_t j = 0; j < nBins - 1; j++)
  {
    float x = xbins[j + 1] - xbins[j];
    binsT->Fill(xbins[j] + 0.5 * x, x);
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

  TH1D *h_jet_hits_energy_frac = new TH1D("h_jet_hit_energy_frac", "Fraction of hit energy", 200, -6, 5);
  h_jet_hits_energy_frac->GetXaxis()->SetTitle("log10 (E [hit] )");

  TH1D *h_jet_hits_energytime_frac = new TH1D("h_jet_hits_energytime_frac", "Fraction of hit energy vs time", 100, 0, 3.5);
  h_jet_hits_energytime_frac->GetXaxis()->SetTitle("log10 (T [ns] )");

  // jet resolution
  static int nmax = 16;
  TH1D *h_jet_res[nmax];
  TH1D *h_jet_ptr[nmax];
  for (int j = 0; j < nmax; j++)
  {
    h_jet_res[j] = new TH1D(Form("jet_resolution_%02d", j), Form("jets_res_%02d", j), 160, 0.0, 2.0);
    h_jet_ptr[j] = new TH1D(Form("jet_resolution_pt_%02d", j), Form("jets_res_pt_%02d", j), 1000, 0, 50000);
    h_jet_res[j]->Sumw2();
  }

  TH1D *h_jet_res_hits[nmax];
  TH1D *h_jet_ptr_hits[nmax];
  for (int j = 0; j < nmax; j++)
  {
    h_jet_res_hits[j] = new TH1D(Form("jet_resolution_hits_%02d", j), Form("jets_res_hits_%02d", j), 160, 0.0, 2.0);
    h_jet_ptr_hits[j] = new TH1D(Form("jet_resolution_hits_pt_%02d", j), Form("jets_res_hits_pt_%02d", j), 1000, 0, 50000);
    h_jet_res_hits[j]->Sumw2();
  }

  TH1D *h_jet_res_hits_raw[nmax];
  TH1D *h_jet_ptr_hits_raw[nmax];
  for (int j = 0; j < nmax; j++)
  {
    h_jet_res_hits_raw[j] = new TH1D(Form("jet_resolution_hits_raw_%02d", j), Form("jets_res_hits_raw_%02d", j), 160, 0.0, 2.0);
    h_jet_ptr_hits_raw[j] = new TH1D(Form("jet_resolution_hits_raw_pt_%02d", j), Form("jets_res_hits_raw_pt_%02d", j), 1000, 0, 50000);
    h_jet_res_hits_raw[j]->Sumw2();
  }

  // raw hits corrected by appropriate sampleing fraction (SF)
  TH1D *h_jet_res_hits_raw_sf[nmax];
  TH1D *h_jet_ptr_hits_raw_sf[nmax];
  //TH2D *h_jet_res_hitstime[nmax];

  for (int j = 0; j < nmax; j++)
  {
    h_jet_res_hits_raw_sf[j] = new TH1D(Form("jet_resolution_hits_raw_sf_%02d", j), Form("jets_res_hits_raw_sf_%02d", j), 160, 0.0, 2.0);
    h_jet_ptr_hits_raw_sf[j] = new TH1D(Form("jet_resolution_hits_raw_sf_pt_%02d", j), Form("jets_res_hits_raw_sf_pt_%02d", j), 1000, 0, 50000);
    h_jet_res_hits_raw_sf[j]->Sumw2();
    //h_jet_res_hitstime[j] = new TH2D(Form("jet_resolution_hitstime_%02d",j), Form("jets_res_hitstime_%02d",j),1000,0.0,0.0001,200,0,2000);
  }

  // track resolution
  TH1D *h_track_res[nmax];
  TH1D *h_track_ptr[nmax];
  for (int j = 0; j < nmax; j++)
  {
    int nbins = 2000 - 10 * j * j; // decreasing number of bins
    if (nbins < 0)
      nbins = 20;
    h_track_res[j] = new TH1D(Form("track_resolution_%02d", j), Form("track_res_%02d", j), nbins, 0.0, 2.0);
    h_track_ptr[j] = new TH1D(Form("track_resolution_pt_%02d", j), Form("track_res_pt_%02d", j), 1000, 0, 50000);
    h_track_res[j]->Sumw2();
  }
  TH1F *Event_number_check_jet = new TH1F("Event_number_check_jet", "Event_number_check_jet", 12, 0, 12);
  TH1F *Event_number_check = new TH1F("Event_number_check", "Event_number_check", 12, 0, 12);
  TH1F *Eta_plot = new TH1F("Eta_plot", "Eta_plot", 200, -10, 10);
  TH1F *Eta_plot_after_cut = new TH1F("Eta_plot_after_cut", "Eta_plot_after_cut", 200, -10, 10);
  TH1F *Timing_Standard = new TH1F("Timing_Standard", "Timing_Standard", 200, 0, 50);
  TH1F *Timing_detecto_ECAL_TDif = new TH1F("Timing_detecto_ECAL_TDif", "Timing_detecto_ECAL_TDif", 200, 0, 50);
  TH1F *Timing_detector_Leading = new TH1F("Timing_detector_Leading", "Timing_detector_Leading", 200, 0, 50);
  TH1F *Timing_detector_Trailing = new TH1F("Timing_detector_Trailing", "Timing_detector_Trailing", 200, 0, 50);
  TH1F *Timing_detector_Average_tem = new TH1F("Timing_detector_Average_tem", "Timing_detector_Average_tem", 1000, 7, 12);
  TH1F *Timing_detector_Average = new TH1F("Timing_detector_Average", "Timing_detector_Average", 200, 0, 50);
  TH1F *Timing_detector_next_to_trailing = new TH1F("Timing_detector_next_to_trailing", "Timing_detector_next_to_trailing", 200, 0, 50);
  TH1F *Timing_detector_Trailing_P = new TH1F("Timing_detector_Trailing_P", "Timing_detector_Trailing_P", 200, 0, 100);
  TH1F *Timing_detector_next_to_trailing_P = new TH1F("Timing_detector_next_to_trailing_P", "Timing_detector_next_to_trailing_P", 200, 0, 100);
  TH1F *Timing_detector_Trailing_V = new TH1F("Timing_detector_Trailing_V", "Timing_detector_Trailing_V", 10000, 8, 9);
  TH1F *Timing_detector_next_to_trailing_V = new TH1F("Timing_detector_next_to_trailing_V", "Timing_detector_next_to_trailing_V", 1000, 0.9, 1);
  TH1F *Timing_detector_dR_Leading_trailing_T = new TH1F("Timing_detector_dR_Leading_trailing_T", "Timing_detector_dR_Leading_trailing_T", 50, 0, 1);
  TH1F *Timing_detector_dR_Leading_next_trailing_T = new TH1F("Timing_detector_dR_Leading_next_trailing_T", "Timing_detector_dR_Leading_next_trailing_T", 50, 0, 1);
  TH1F *Timing_detector_dR_Leading_trailing_PT = new TH1F("Timing_detector_dR_Leading_trailing_PT", "Timing_detector_dR_Leading_trailing_PT", 50, 0, 1);
  TH1F *Timing_detector_dR_Leading_next_trailing_PT = new TH1F("Timing_detector_dR_Leading_next_trailing_PT", "Timing_detector_dR_Leading_next_trailing_PT", 50, 0, 1);
  TH1F *Timing_detector_dR_Leading_Proton_PT = new TH1F("Timing_detector_dR_Leading_Proton_PT", "Timing_detector_dR_Leading_Proton_PT", 50, 0, 1);

  TH2F *Timing_momentum_correlation = new TH2F("Timing_momentum_correlation", "Timing_momentum_correlation", 20, 0, 1, 20, 0, 1);
  TH2F *Timing_P_rank_difference_momentum_correlation = new TH2F("Timing_P_rank_difference_momentum_correlation", "Timing_P_rank_difference_momentum_correlation", 6, 0, 3, 40, -2, 2);
  TH1F *mass_sum_average = new TH1F("mass_sum_average", "mass_sum_average", 100, 0.5, 2.5);
  TH1F *mass_sum_average_Reco = new TH1F("mass_sum_average_Reco", "mass_sum_average_Reco", 200, 0.5, 4.5);
  TH1F *mass_sum_average_Reco_track = new TH1F("mass_sum_average_Reco_track", "mass_sum_average_Reco_track", 200, 0.5, 4.5);

  TH1F *check_jet_particle_number = new TH1F("check_jet_particle_number", "check_jet_particle_number", 100, 0, 100);
  TH1F *Highest_rank = new TH1F("Highest_rank", "Highest_rank", 100, 0, 100);
  TH1F *Total_particle_ID_no_cut = new TH1F("Total_particle_ID_no_cut", "Total_particle_ID_no_cut", 20, 0, 20);
  TH1F *Total_particle_ID_eta_cut = new TH1F("Total_particle_ID_eta_cut", "Total_particle_ID_eta_cut", 20, 0, 20);
  TH1F *Total_particle_ID_eta_PT_cut = new TH1F("Total_particle_ID_eta_PT_cut", "Total_particle_ID_eta_PT_cut", 20, 0, 20);
  TH1F *Total_particle_ID_cut = new TH1F("Total_particle_ID_cut", "Total_particle_ID_cut", 5000, 0, 5000);
  TH1F *Baryon_cut_PT = new TH1F("Baryon_cut_PT", "Baryon_cut_PT", 2000, 0, 1000);
  //==============Trailing_particle_ID============//
  TH1F *Trailing_particle_ID_T = new TH1F("Trailing_particle_ID_T", "Trailing_particle_ID_T", 20, 0, 20);
  TH1F *Trailing_particle_ID_PT = new TH1F("Trailing_particle_ID_PT", "Trailing_particle_ID_PT", 20, 0, 20);
  TH1F *Next_to_trailing_particle_ID_T = new TH1F("Next_to_trailing_particle_ID_T", "Next_to_trailing_particle_ID_T", 20, 0, 20);
  TH1F *Next_to_trailing_particle_ID_PT = new TH1F("Next_to_trailing_particle_ID_PT", "Next_to_trailing_particle_ID_PT", 20, 0, 20);
  //=============TH2F_Trailing_ID_PT==============//

  TH1F *Timing_detector_Reco_TOF = new TH1F("Timing_detector_Reco_TOF", "Timing_detector_Reco_TOF", 200, 0, 50);
  TH1F *Timing_detector_Reco_TOF_track = new TH1F("Timing_detector_Reco_TOF_track", "Timing_detector_Reco_TOF_track", 200, 0, 50);

  TH1F *h_Particles_Rank_T[5];
  TH1F *h_Particles_Rank_PT[5];
  for (int j = 0; j < 5; j++)
  {
    h_Particles_Rank_T[j] = new TH1F(Form("h_Particles_Rank_T_%i", j), Form("h_Particles_Rank_T_%i", j), 20, 0, 20);
    h_Particles_Rank_PT[j] = new TH1F(Form("h_Particles_Rank_PT_%i", j), Form("h_Particles_Rank_PT_%i", j), 20, 0, 20);
  }

  TH2F *h_Particles_Rank_T_vs_PT[5];
  TH2F *h_Particles_Rank_PT_vs_PT[5];
  for (int j = 0; j < 5; j++)
  {
    h_Particles_Rank_T_vs_PT[j] = new TH2F(Form("h_Particles_Rank_T_vs_PT%i", j), Form("h_Particles_Rank_T_vs_PT%i", j), 20, 0, 20, 16, -2, 6);
    h_Particles_Rank_PT_vs_PT[j] = new TH2F(Form("h_Particles_Rank_PT_vs_PT%i", j), Form("h_Particles_Rank_PT_vs_PT%i", j), 20, 0, 20, 16, -2, 6);
  }

  TH2F *h_Particles_Rank_T_vs_T[5];
  TH2F *h_Particles_Rank_PT_vs_T[5];
  for (int j = 0; j < 5; j++)
  {
    h_Particles_Rank_T_vs_T[j] = new TH2F(Form("h_Particles_Rank_T_vs_T%i", j), Form("h_Particles_Rank_T_vs_T%i", j), 20, 0, 20, 500, 0, 50);
    h_Particles_Rank_PT_vs_T[j] = new TH2F(Form("h_Particles_Rank_PT_vs_T%i", j), Form("h_Particles_Rank_PT_vs_T%i", j), 20, 0, 20, 500, 0, 50);
  }

  TH1F *h_Jet_PT = new TH1F("h_Jet_PT", "h_Jet_PT", 5000, 0, 5000);
  TH1F *h_Jet_SM_PT_PT = new TH1F("h_Jet_SM_PT_PT", "h_Jet_SM_PT_PT", 80, -2, 6);
  TH1F *h_Jet_SM_PT_T = new TH1F("h_Jet_SM_PT_T", "h_Jet_SM_PT_T", 5000, 0, 50);
  TH1F *h_Jet_T_PT = new TH1F("h_Jet_T_PT", "h_Jet_T_PT", 80, -2, 6);
  TH1F *h_Jet_T_T = new TH1F("h_Jet_T_T", "h_Jet_T_T", 5000, 0, 50);
  TH1F *h_Jet_PT_HI_PT_C_P = new TH1F("h_Jet_PT_HI_PT_C_P", "h_Jet_PT_HI_PT_C_P", 100, 0, 1);

  TH1F *h_Particles_Rank_T_Reco[5];
  TH1F *h_Particles_Rank_PT_Reco[5];
  for (int j = 0; j < 5; j++)
  {
    h_Particles_Rank_T_Reco[j] = new TH1F(Form("h_Particles_Rank_T_Reco_%i", j), Form("h_Particles_Rank_T_Reco_%i", j), 30, 0, 30);
    h_Particles_Rank_PT_Reco[j] = new TH1F(Form("h_Particles_Rank_PT_Reco_%i", j), Form("h_Particles_Rank_PT_Reco_%i", j), 30, 0, 30);
  }

  TH1F *h_Particles_dR_Highest_PT_T[5];
  TH1F *h_Particles_dR_Highest_PT_PT[5];
  for (int j = 0; j < 5; j++)
  {
    h_Particles_dR_Highest_PT_T[j] = new TH1F(Form("h_Particles_dR_Highest_PT_T_%i", j), Form("h_Particles_dR_Highest_PT_T_%i", j), 100, 0, 1);
    h_Particles_dR_Highest_PT_PT[j] = new TH1F(Form("h_Particles_dR_Highest_PT_PT_%i", j), Form("h_Particles_dR_Highest_PT_PT_%i", j), 100, 0, 1);
  }
  TH1F *h_Particles_dR_Highest_PT_T_Reco[5];
  TH1F *h_Particles_dR_Highest_PT_PT_Reco[5];
  for (int j = 0; j < 5; j++)
  {
    h_Particles_dR_Highest_PT_T_Reco[j] = new TH1F(Form("h_Particles_dR_Highest_PT_T_Reco_%i", j), Form("h_Particles_dR_Highest_PT_T_Reco_%i", j), 100, 0, 1);
    h_Particles_dR_Highest_PT_PT_Reco[j] = new TH1F(Form("h_Particles_dR_Highest_PT_PT_Reco_%i", j), Form("h_Particles_dR_Highest_PT_PT_Reco_%i", j), 100, 0, 1);
  }
  TH1F *h_Particles_dR_Highest_PT_T_Reco_track[5];
  TH1F *h_Particles_dR_Highest_PT_PT_Reco_track[5];
  for (int j = 0; j < 5; j++)
  {
    h_Particles_dR_Highest_PT_T_Reco_track[j] = new TH1F(Form("h_Particles_dR_Highest_PT_T_Reco_track%i", j), Form("h_Particles_dR_Highest_PT_T_Reco_track%i", j), 100, 0, 1);
    h_Particles_dR_Highest_PT_PT_Reco_track[j] = new TH1F(Form("h_Particles_dR_Highest_PT_PT_Reco_track%i", j), Form("h_Particles_dR_Highest_PT_PT_Reco_track%i", j), 100, 0, 1);
  }

  TH1F *Baryons_ID = new TH1F("Baryons_ID", "Baryons_ID", 20, 0, 20);
  TH1F *Check_matching_0P2 = new TH1F("Check_matching_0P2", "Check_matching_0P2", 6, -1, 5);
  TH1F *Check_matching_0P3 = new TH1F("Check_matching_0P3", "Check_matching_0P3", 6, -1, 5);
  TH1F *Check_matching_0P4 = new TH1F("Check_matching_0P4", "Check_matching_0P4", 6, -1, 5);

  TH1F *check_Pion_DZ = new TH1F("check_Pion_DZ", "check_Pion_DZ", 50, 0, 5);
  TH1F *check_Proton_DZ = new TH1F("check_Pion_DZ", "check_Proton_DZ", 50, 0, 5);
  TH1F *check_Pion_VZ = new TH1F("check_Pion_VZ", "check_Pion_VZ", 10000, 0.9, 1);
  TH1F *check_Proton_V = new TH1F("check_Proton_V", "check_Proton_V", 2000, 0.9, 1);
  TH1F *check_Pion_T = new TH1F("check_Pion_T", "check_Pion_T", 200, 0, 50);
  TH1F *check_Proton_T = new TH1F("check_Proton_T", "check_Proton_T", 200, 0, 50);

  Int_t Event;
  Int_t ID_Tr0T;
  Int_t ID_Tr1T;
  Int_t ID_Tr2T;
  Int_t ID_Tr3T;
  Int_t ID_Tr4T;
  Int_t ID_Tr0PT;
  Int_t ID_Tr1PT;
  Int_t ID_Tr2PT;
  Int_t ID_Tr3PT;
  Int_t ID_Tr4PT;
  Float_t PT_Tr0T_HPt;
  Float_t PT_Tr1T_HPt;
  Float_t PT_Tr2T_HPt;
  Float_t PT_Tr3T_HPt;
  Float_t PT_Tr4T_HPt;
  Float_t PT_Tr0PT_HPt;
  Float_t PT_Tr1PT_HPt;
  Float_t PT_Tr2PT_HPt;
  Float_t PT_Tr3PT_HPt;
  Float_t PT_Tr4PT_HPt;
  TTree *T = new TTree("BDT_variables", "BDT_variables");
  T->Branch("Event", &Event, "Event/I");
  T->Branch("PT_Tr0T_HPt", &PT_Tr0T_HPt, "PT_Tr0T_HPt/F");
  T->Branch("PT_Tr1T_HPt", &PT_Tr1T_HPt, "PT_Tr1T_HPt/F");
  T->Branch("PT_Tr2T_HPt", &PT_Tr2T_HPt, "PT_Tr2T_HPt/F");
  T->Branch("PT_Tr3T_HPt", &PT_Tr3T_HPt, "PT_Tr3T_HPt/F");
  T->Branch("PT_Tr4T_HPt", &PT_Tr4T_HPt, "PT_Tr4T_HPt/F");
  T->Branch("PT_Tr0PT_HPt", &PT_Tr0PT_HPt, "PT_Tr0PT_HPt/F");
  T->Branch("PT_Tr1PT_HPt", &PT_Tr1PT_HPt, "PT_Tr1PT_HPt/F");
  T->Branch("PT_Tr2PT_HPt", &PT_Tr2PT_HPt, "PT_Tr2PT_HPt/F");
  T->Branch("PT_Tr3PT_HPt", &PT_Tr3PT_HPt, "PT_Tr3PT_HPt/F");
  T->Branch("PT_Tr4PT_HPt", &PT_Tr4PT_HPt, "PT_Tr4PT_HPt/F");

  /*
  T->Branch("dR_Tr0T_HPt",&dR_Tr0T_HPt,"dR_Tr0T_HPt/F");
  T->Branch("dR_Tr1T_HPt",&dR_Tr1T_HPt,"dR_Tr1T_HPt/F");
  T->Branch("dR_Tr2T_HPt",&dR_Tr2T_HPt,"dR_Tr2T_HPt/F");
  T->Branch("dR_Tr3T_HPt",&dR_Tr3T_HPt,"dR_Tr3T_HPt/F");
  T->Branch("dR_Tr4T_HPt",&dR_Tr4T_HPt,"dR_Tr4T_HPt/F");
  T->Branch("dR_Tr0PT_HPt",&dR_Tr0PT_HPt,"dR_Tr0PT_HPt/F");
  T->Branch("dR_Tr1PT_HPt",&dR_Tr1PT_HPt,"dR_Tr1PT_HPt/F");
  T->Branch("dR_Tr2PT_HPt",&dR_Tr2PT_HPt,"dR_Tr2PT_HPt/F");
  T->Branch("dR_Tr3PT_HPt",&dR_Tr3PT_HPt,"dR_Tr3PT_HPt/F");
  T->Branch("dR_Tr4PT_HPt",&dR_Tr4PT_HPt,"dR_Tr4PT_HPt/F");
  T->Branch("ID_Tr0T",&ID_Tr0T,"ID_Tr0T/I");
  T->Branch("ID_Tr1T",&ID_Tr1T,"ID_Tr1T/I");
  T->Branch("ID_Tr2T",&ID_Tr2T,"ID_Tr2T/I");
  T->Branch("ID_Tr3T",&ID_Tr3T,"ID_Tr3T/I");
  T->Branch("ID_Tr4T",&ID_Tr4T,"ID_Tr4T/I");
  T->Branch("ID_Tr0PT",&ID_Tr0PT,"ID_Tr0PT/I");
  T->Branch("ID_Tr1PT",&ID_Tr1PT,"ID_Tr1PT/I");
  T->Branch("ID_Tr2PT",&ID_Tr2PT,"ID_Tr2PT/I");
  T->Branch("ID_Tr3PT",&ID_Tr3PT,"ID_Tr3PT/I");
  T->Branch("ID_Tr4PT",&ID_Tr4PT,"ID_Tr4PT/I");
  */

  Int_t Event_reco;
  Float_t dR_Tr0T_HPt_Reco;
  Float_t dR_Tr1T_HPt_Reco;
  Float_t dR_Tr2T_HPt_Reco;
  Float_t dR_Tr3T_HPt_Reco;
  Float_t dR_Tr4T_HPt_Reco;
  Float_t dR_Tr0PT_HPt_Reco;
  Float_t dR_Tr1PT_HPt_Reco;
  Float_t dR_Tr2PT_HPt_Reco;
  Float_t dR_Tr3PT_HPt_Reco;
  Float_t dR_Tr4PT_HPt_Reco;
  TTree *T_Reco_T = new TTree("BDT_variables_Reco", "BDT_variables_Reco");
  T_Reco_T->Branch("Event_reco", &Event_reco, "Event_reco/I");
  T_Reco_T->Branch("dR_Tr0T_HPt_Reco", &dR_Tr0T_HPt_Reco, "dR_Tr0T_HPt_Reco/F");
  T_Reco_T->Branch("dR_Tr1T_HPt_Reco", &dR_Tr1T_HPt_Reco, "dR_Tr1T_HPt_Reco/F");
  T_Reco_T->Branch("dR_Tr2T_HPt_Reco", &dR_Tr2T_HPt_Reco, "dR_Tr2T_HPt_Reco/F");
  T_Reco_T->Branch("dR_Tr3T_HPt_Reco", &dR_Tr3T_HPt_Reco, "dR_Tr3T_HPt_Reco/F");
  T_Reco_T->Branch("dR_Tr4T_HPt_Reco", &dR_Tr4T_HPt_Reco, "dR_Tr4T_HPt_Reco/F");
  T_Reco_T->Branch("dR_Tr0PT_HPt_Reco", &dR_Tr0PT_HPt_Reco, "dR_Tr0PT_HPt_Reco/F");
  T_Reco_T->Branch("dR_Tr1PT_HPt_Reco", &dR_Tr1PT_HPt_Reco, "dR_Tr1PT_HPt_Reco/F");
  T_Reco_T->Branch("dR_Tr2PT_HPt_Reco", &dR_Tr2PT_HPt_Reco, "dR_Tr2PT_HPt_Reco/F");
  T_Reco_T->Branch("dR_Tr3PT_HPt_Reco", &dR_Tr3PT_HPt_Reco, "dR_Tr3PT_HPt_Reco/F");
  T_Reco_T->Branch("dR_Tr4PT_HPt_Reco", &dR_Tr4PT_HPt_Reco, "dR_Tr4PT_HPt_Reco/F");

  Int_t Event_reco_track;
  Float_t dR_Tr0T_HPt_Reco_track;
  Float_t dR_Tr1T_HPt_Reco_track;
  Float_t dR_Tr2T_HPt_Reco_track;
  Float_t dR_Tr3T_HPt_Reco_track;
  Float_t dR_Tr4T_HPt_Reco_track;
  Float_t dR_Tr0PT_HPt_Reco_track;
  Float_t dR_Tr1PT_HPt_Reco_track;
  Float_t dR_Tr2PT_HPt_Reco_track;
  Float_t dR_Tr3PT_HPt_Reco_track;
  Float_t dR_Tr4PT_HPt_Reco_track;
  TTree *T_Reco_T_track = new TTree("BDT_variables_Reco_track", "BDT_variables_Reco_track");
  T_Reco_T_track->Branch("Event_reco_track", &Event_reco_track, "Event_reco_track/I");
  T_Reco_T_track->Branch("dR_Tr0T_HPt_Reco_track", &dR_Tr0T_HPt_Reco_track, "dR_Tr0T_HPt_Reco_track/F");
  T_Reco_T_track->Branch("dR_Tr1T_HPt_Reco_track", &dR_Tr1T_HPt_Reco_track, "dR_Tr1T_HPt_Reco_track/F");
  T_Reco_T_track->Branch("dR_Tr2T_HPt_Reco_track", &dR_Tr2T_HPt_Reco_track, "dR_Tr2T_HPt_Reco_track/F");
  T_Reco_T_track->Branch("dR_Tr3T_HPt_Reco_track", &dR_Tr3T_HPt_Reco_track, "dR_Tr3T_HPt_Reco_track/F");
  T_Reco_T_track->Branch("dR_Tr4T_HPt_Reco_track", &dR_Tr4T_HPt_Reco_track, "dR_Tr4T_HPt_Reco_track/F");
  T_Reco_T_track->Branch("dR_Tr0PT_HPt_Reco_track", &dR_Tr0PT_HPt_Reco_track, "dR_Tr0PT_HPt_Reco_track/F");
  T_Reco_T_track->Branch("dR_Tr1PT_HPt_Reco_track", &dR_Tr1PT_HPt_Reco_track, "dR_Tr1PT_HPt_Reco_track/F");
  T_Reco_T_track->Branch("dR_Tr2PT_HPt_Reco_track", &dR_Tr2PT_HPt_Reco_track, "dR_Tr2PT_HPt_Reco_track/F");
  T_Reco_T_track->Branch("dR_Tr3PT_HPt_Reco_track", &dR_Tr3PT_HPt_Reco_track, "dR_Tr3PT_HPt_Reco_track/F");
  T_Reco_T_track->Branch("dR_Tr4PT_HPt_Reco_track", &dR_Tr4PT_HPt_Reco_track, "dR_Tr4PT_HPt_Reco_track/F");

  // read detector geometry for this configuration
  string detector = "./data/rfull009_sifcch7/sifcch7/sifcch7.pandora";
  DetectorGeometrySimple *geom = new DetectorGeometrySimple(detector);
  string caloType = "HAD_BARREL";
  DetectorGeometrySimple::ExtraSubDetectorParameters *xsubdet = geom->getExtraSubDetectorParametersFromType(caloType);
  if (xsubdet == NULL)
  {
    std::cout << "The ExtraSubDetectorParameters for " << caloType << " were not found." << std::endl;
    throw new std::exception;
  }

  string caloType_ecal = "EM_BARREL";
  DetectorGeometrySimple::ExtraSubDetectorParameters *xsubdet_ecal = geom->getExtraSubDetectorParametersFromType(caloType_ecal);
  if (xsubdet_ecal == NULL)
  {
    std::cout << "The ExtraSubDetectorParameters for " << caloType_ecal << " were not found." << std::endl;
    throw new std::exception;
  }

  // Get the decoder.
  IDDecoder *decoder = xsubdet->m_decoder;
  IDDecoder *decoder_ecal = xsubdet_ecal->m_decoder;

  // calculate position
  double layer_size_mm = 27.5 + 5 + 2.5;
  double hcal_inner_R_mm = 2300;

  double layer_size_ecal_mm = 4.0;
  double ecal_inner_R_mm = 2100;

  // calculate weighted average of time
  double XTime = 0;
  double XEnergy = 0;

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

  const char *tupleNames = "px:py:pz:vx:vy:vz:ex:ey:ez:pdg:np:nd:gs:ss";
  TNtupleD *tuple = new TNtupleD("MCParticle", "", tupleNames);

  double minPtConst = 0.2; // min pT on constituents
  // jets
  double Rparam = 0.4;
  const double ETAmax = 1.0;
  double ETmin = 0.5;
  if (mtype == 1)
    ETmin = 25; // increase for boosted
  if (mtype == 31)
    ETmin = 50;
  if (mtype == 32)
    ETmin = 2000;
  if (mtype == 33)
    ETmin = 8000;

  if (mtype == 1)
    cout << "mu+mu- mode for boosted jets" << endl;
  if (mtype == 2)
    cout << "single-particle mode for pgun" << endl;
  if (mtype == 3)
    cout << "pp mode for jet resolutions" << endl;

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

  int MaxEvents = 100000000;

  int nEvents = 0;
  int Hadronic_decay_total = 0;
  int Leptonic_decay_total = 0;
  vector<int> Total_particle_kind = {11, 12, 13, 14, 22, 130, 211, 310, 321, 2112, 2212, 3112, 3122, 3312, 3222, 3322, 16, 3334};
  vector<int> Trailing_particle_kind = {11, 13, 130, 211, 321, 2112, 2212, 3122, 3112, 3312, 3222, 3322, 16, 3334, 1000010020, 310};
  vector<int> Trailing_particle_kind_limit = {11, 13, 130, 211, 321, 2112, 2212};
  vector<int> Trailing_particle_kind_limit_pT = {11, 13, 211, 321, 2212};
  vector<int> Trailing_particle_kind_T = {11, 12, 13, 14, 22, 130, 211, 310, 321, 2112, 2212, 3112, 3122, 3312, 3222, 3322, 16, 3334, 1000010020};
  vector<int> Trailing_particle_kind_PT = {11, 12, 13, 14, 22, 130, 211, 310, 321, 2112, 2212, 3112, 3122, 3312, 3222, 3322, 16, 3334, 1000010020};
  vector<double> Trailing_particle_kind_mass = {0.0005, 0, 0.1057, 0, 0, 0.497648, 0.1349766, 0.497648, 0.493, 0.938, 0.939, 1.197, 1.115, 1.321, 1.189, 1.314, 0, 1.672, 1.86};
  vector<int> Baryons_particle_kind = {2112, 2212, 3112, 3122, 3312, 3222, 3322};
  int Trailing_photon = 0;
  int Forth = 1;
  int Back = -1;
  vector<int> Check_Forth_And_Back = {Forth, Back};

  vector<LParticle> SimHIT;
  // loop over all files
  for (unsigned int mfile = 0; mfile < files.size(); mfile++)
  {

    string Rfile = files[mfile];
    cout << "string of Rfile: " << Rfile << endl;
    vector<int> Process_number;
    if ((Rfile).find("_qq_") > 0 and (Rfile).find("_qq_") < 1000)
    {
      cout << "QQ coming!" << endl;
      Process_number.push_back(0);
    }
    if ((Rfile).find("_ww_") > 0 and (Rfile).find("_ww_") < 1000)
    {
      cout << "WW coming!" << endl;
      Process_number.push_back(1);
    }
    if ((Rfile).find("_tt_") > 0 and (Rfile).find("_tt_") < 1000)
    {
      cout << "tt coming!" << endl;
      Process_number.push_back(2);
    }

    cout << "Process_number: " << Process_number[0] << endl;
    cout << " # File=" << Rfile << endl;
    IO::LCReader *lcReader = IOIMPL::LCFactory::getInstance()->createLCReader();
    lcReader->open(Rfile.c_str());
    cout << "File_name" << Rfile.c_str() << endl;

    EVENT::LCEvent *evt = 0;

    if (nEvents > MaxEvents)
      break;
    //if (nEvents>1) break;
    //----------- the event loop -----------
    while ((evt = lcReader->readNextEvent()) != 0)
    {
      if (nEvents == 0)
        UTIL::LCTOOLS::dumpEvent(evt);

      // UTIL::LCTOOLS::dumpEvent( evt ) ;

      nEvents++;
      cout << "nEvents: " << nEvents << endl;
      cout << " # Events=" << nEvents << endl;
      Event_number_check->Fill(1);
      Event = nEvents;
      Event_reco = nEvents;

      //Event_reco_track = nEvents;
      int Status0 = 0;
      int Status1 = 0;
      int Status2 = 0;
      int Status3 = 0;
      vector<int> No_charge_PDG;

      // cout << "aaa.size(): " << aaa.size() << endl;

      //if (nEvents!=1870) continue;
      if (nEvents > MaxEvents)
        break;

      h_debug->Fill(1.0);

      std::string mcpName("MCParticle");
      // get truth
      IMPL::LCCollectionVec *col = (IMPL::LCCollectionVec *)evt->getCollection(mcpName);
      int nMCP = col->getNumberOfElements();
      //cout << "nMCP: " << nMCP << endl;
      int neu = 0;

      vector<PseudoJet> avec_truth;     // created by generator
      vector<PseudoJet> avec_truth_sim; // also created by geant
      cout << "truth-1: ";
      //==============================================================//
      vector<bool> Check_Forth_And_Back_Bool;
      vector<TLorentzVector> Forth_And_Back_Vector;
      int Zprime_pdg = 32;
      int Photon_pdg = 22;
      int Muon_pdg = 13;
      int W_pdg = 24;
      //Check the leptonic decay and hadronic decay
      for (int CFAB = 0; CFAB < 2; CFAB++)
      {
        int Leptonic_check = 0;
        for (int i = 0; i < nMCP; ++i)
        {
          EVENT::MCParticle *mcp = (EVENT::MCParticle *)col->getElementAt(i);
          if (mcp->getParents().size() != 0)
          {
            if ((mcp->getParents()[0]->getPDG() == 32) and (mcp->getPDG()) * Check_Forth_And_Back[CFAB] > 0 and (mcp->getGeneratorStatus() == 3))
            {
              TLorentzVector p;
              p.SetPxPyPzE(mcp->getMomentum()[0], mcp->getMomentum()[1], mcp->getMomentum()[2], mcp->getMomentum()[3]);
              Forth_And_Back_Vector.push_back(p);
              //cout << "mcp->getPDG(): " << mcp->getPDG() << endl;
              for (int j = 0; j < (mcp->getDaughters().size()); j++)
              {
                if ((abs(mcp->getDaughters()[j]->getPDG()) < 19) and (abs(mcp->getDaughters()[j]->getPDG()) > 10))
                  Leptonic_check = Leptonic_check + 1;
              }
            }
          }
        }

        if (Leptonic_check != 0)
        {
          Leptonic_decay_total = Leptonic_decay_total + 1;
        }
        else
        {
          Hadronic_decay_total = Hadronic_decay_total + 1;
        }

        if (Leptonic_check != 0)
        {
          cout << "Awful leptonic decay:" << endl;
          Check_Forth_And_Back_Bool.push_back(false);
        }
        else
        {
          cout << "Good Jet! Hadronic decay:" << endl;
          Check_Forth_And_Back_Bool.push_back(true);
        }
      }
      if (Check_Forth_And_Back_Bool[0] == false and Check_Forth_And_Back_Bool[1] == false)
        continue;
      cout << "truth-2: ";
      //==============================================================//
      int Real_particle = 0;
      vector<int> PDG_with_no_charge = {0};
      for (int i = 0; i < nMCP; ++i)
      {
        EVENT::MCParticle *mcp = (EVENT::MCParticle *)col->getElementAt(i);
        //cout << "i: " << i << endl;
        double px = mcp->getMomentum()[0];
        double py = mcp->getMomentum()[1];
        double pz = mcp->getMomentum()[2];
        double m = mcp->getMomentum()[3];
        double e = sqrt(px * px + py * py + pz * pz + m * m);
        int pdgid = mcp->getPDG();
        //cout << "1" << endl;
        if (mcp->getCharge() == 0)
        {
          //cout << "yes llop" << endl;
          int itt;
          itt = find(PDG_with_no_charge.begin(), PDG_with_no_charge.end(), abs(pdgid))[0]; //return 2u
          if (itt != abs(pdgid))
          {
            PDG_with_no_charge.push_back(abs(pdgid));
          }

          //for(int j=0 ; j<PDG_with_no_charge.size(); j++) cout << "PDG_with_no_charge: " << PDG_with_no_charge[j] << endl;
        }
        //cout << "2" << endl;
        //     if(pdgid==211) cout << "mcp->getCharge(): " << mcp->getCharge() << endl;
        //if(pdgid==22) cout << "Yes we have 22 particle" << endl;
        //TLorentzVector p;
        //p.SetPxPyPzE(px,py,pz,e);
        fastjet::PseudoJet p(px, py, pz, e);
        p.set_user_index(pdgid);
        // find high-pT neutrino
        /*
      if ( (mcp->getPDG() == 12 || mcp->getPDG() == 14 || mcp->getPDG() == 16) && p.Pt()>100 ) {
      neu++;
      }

      // includes Geant4 and backscatter too
      bool isGeant4=false;
      if (abs(p.PseudoRapidity()) < 2.0 && (mcp->isCreatedInSimulation()==true || mcp->isBackscatter() ==true) && p.Pt()>minPtConst) {
          if (mcp->getPDG() != 12 && mcp->getPDG() != 14 && mcp->getPDG() != 16 ) isGeant4=true;
      }
	*/
        bool isGeant4 = false;
        // generator-level
        bool isGen = true;
        //if (abs(p.PseudoRapidity()) < 2.0 && mcp->getGeneratorStatus()==2 && p.Pt()>minPtConst) {
        //if (mcp->getPDG() != 12 && mcp->getPDG() != 14 && mcp->getPDG() != 16 ) isGen=true;
        //}

        // only generator level
        if (isGen == true)
        {

          int pdg = mcp->getPDG();
          int np = mcp->getParents().size();
          int nd = mcp->getDaughters().size();
          int gs = mcp->getGeneratorStatus();
          /*
{	
      cout << "px: " << px << "py: " <<py <<  "pz: " << pz << endl;
      for(int j=0 ; j<np ; j++)cout << "mcp->getParents()" << mcp->getParents()[j]->getPDG();
      for(int j=0 ; j<nd ; j++)cout << "mcp->getDaughters()" << mcp->getDaughters()[j]->getPDG();
      //for(int j=0 ; j<np ; j++)cout << "mcp->getParents()" << mcp->getParents()[j]->getPDG();
      cout << "pdg: " << pdg << endl;
      cout << "np: " << np << endl;
      cout << "nd: " << nd << endl;
      cout << "gs: " << gs << endl;}
*/
          if (abs(pdg) == 22 and gs == 1 and abs(mcp->getParents()[0]->getPDG()) == 13 and abs(mcp->getParents()[0]->getMomentum()[2]) > 2000)
          {
            //cout << "ISR_Photon_cut_off" << endl;
            continue;
          }
          if (gs == 0)
            Status0 = Status0 + 1;
          if (gs == 1)
            Status1 = Status1 + 1;
          if (gs == 2)
            Status2 = Status2 + 1;
          if (gs == 3)
            Status3 = Status3 + 1;
          if (gs == 1)
          {
            avec_truth.push_back(p);
            //cout << "test5 = " << avec_truth.size() << endl;
            /*
        if(pdg>0){if(Check_Forth_And_Back_Bool[0]==1){//cout << "pdg: "<< pdg << endl;
							avec_truth.push_back(p);}}
        if(pdg<0){if(Check_Forth_And_Back_Bool[1]==1){//cout << "pdg: "<< pdg << endl;
							avec_truth.push_back(p);}}
	*/
          }
        }
        /*
      // plus Geant4
      if (isGen==true || isGeant4==true) {
      int pdg = mcp->getPDG() ;
      int np = mcp->getParents().size() ;
      int nd = mcp->getDaughters().size() ;
      inzt gs = mcp->getGeneratorStatus() ;
      int ss = mcp->getSimulatorStatus() ;
      //cout << mcp->getSimulatorStatus() << " " << mcp->getPDG() << endl;
      //tuple->Fill(px,py,pz,vx,vy,vz,ex,ey,ez,pdg,np,nd,gs,ss) ;
      avec_truth_sim.push_back( PseudoJet(px,py,pz,e) );
    }*/
      }
      //   for(int j=0 ; j<PDG_with_no_charge.size() ; j++) cout << "PDG_with_no_charge: " << PDG_with_no_charge[j] << endl;
      //cout << "Status0 : " << Status0 << endl;
      //cout << "Status1 : " << Status1 << endl;
      //cout << "Status2 : " << Status2 << endl;
      //cout << "Status3 : " << Status3 << endl;
      //cout << avec_truth_sim.size() << " gen=" << avec_truth.size() << endl;

      cout << "truth-3: ";
      // assume remnant for mu+mu-
      if (mtype == 1)
      {
        //avec_truth.push_back( PseudoJet(0,0,5000,5000) );
        //avec_truth.push_back( PseudoJet(0,0,-5000,5000) );
      }

      int activeAreaRepeats = 1;
      double ghostArea = 0.01;
      double ghostEtaMax = 7.0;
      fastjet::GhostedAreaSpec fjActiveArea(ghostEtaMax, activeAreaRepeats, ghostArea);
      fastjet::AreaDefinition fjAreaDefinition(fastjet::active_area, fjActiveArea);
      fastjet::ClusterSequenceArea *thisClustering = new fastjet::ClusterSequenceArea(avec_truth, jet_def, fjAreaDefinition);
      vector<fastjet::PseudoJet> sjets_truth = sorted_by_pt(thisClustering->inclusive_jets(25.0));
      vector<LParticle> truthjets;
      int nn = 0;
      int check = 4;
      int Jet_each_event = 0;
      vector<TLorentzVector> Truthjets_axis;

      cout << "truth-4: ";
      cout << sjets_truth.size() << endl;
      for (unsigned int k = 0; k < sjets_truth.size(); k++)
      {
        double ptt = sjets_truth[k].perp();
        h_jet_pt_truth_sim->Fill(ptt);

        //            cout << "sjets_truth[k].constituents().size(): " << sjets_truth[k].constituents().size() << endl;
        //for(int j = 0 ; j < sjets_truth[k].constituents().size(); j++) cout << "pdg: " << sjets_truth[k].constituents()[j].user_index() << endl;
        if (sjets_truth[k].constituents().size() == 1 and abs(sjets_truth[k].constituents()[0].user_index()) == 22)
        { //cout << "Fucking ISR Photon" << endl;
          continue;
        }
        double eta = sjets_truth[k].pseudorapidity();
        double phi = sjets_truth[k].phi();
        if (phi < 0)
          phi = phi + k2PI;
        double m = sjets_truth[k].m();
        double pt = sjets_truth[k].perp();
        double e = sjets_truth[k].e();
        vector<float> velocity_jet;
        vector<float> velocity_jet_sort;
        vector<float> momentum_jet;
        vector<float> PT_jet;
        vector<float> PT_jet_sort;
        vector<int> constit_PDG;
        vector<float> velocity_jet_Z;
        vector<float> velocity_jet_Theta;
        vector<float> jet_time;
        vector<float> jet_time_sort;
        TLorentzVector p_using;
        vector<float> P_jet_sort;

        vector<float> jet_time_for_rank_sort;
        vector<float> jet_time_for_rank;
        vector<float> jet_P_for_rank_sort;
        vector<float> jet_P_for_rank;
        vector<int> Rank_PDGID;

        p_using.SetPxPyPzE(sjets_truth[k].px(), sjets_truth[k].py(), sjets_truth[k].pz(), sjets_truth[k].e());

        fastjet::PseudoJet Jet_axis(sjets_truth[k].px(), sjets_truth[k].py(), sjets_truth[k].pz(), sjets_truth[k].e());

        if (p_using.DeltaR(Forth_And_Back_Vector[0]) < 0.1 * check and Check_Forth_And_Back_Bool[0] == 0)
        {
          cout << "backward jet1" << endl;
          continue;
        }
        if (p_using.DeltaR(Forth_And_Back_Vector[1]) < 0.1 * check and Check_Forth_And_Back_Bool[1] == 0)
        {
          cout << "backward jet2" << endl;
          continue;
        }
        if (p_using.DeltaR(Forth_And_Back_Vector[0]) > 0.1 * check and p_using.DeltaR(Forth_And_Back_Vector[1]) > 0.1 * check)
        {
          continue;
        }
        float Jet_PT = p_using.Perp();
        Jet_each_event = Jet_each_event + 1;
        h_Jet_PT->Fill(p_using.Perp());
        cout << "p_using.Perp: " << p_using.Perp() << endl;
        LParticle p(sjets_truth[k].px(), sjets_truth[k].py(), sjets_truth[k].pz(), sjets_truth[k].e(), 0);
        vector<PseudoJet> constit = sjets_truth[k].constituents();
        int csize = constit.size();
        float event_number = 0;
        float Event_number_out_Eta2P1 = 0;
        float time_average = 0;
        float mass_average = 0;
        float SOL = 3 * TMath::Power(10, 8);
        int Trailing_particle_ID_size = Trailing_particle_kind.size();
        int Check_photon_jet = 0;
        vector<TLorentzVector> FourP;
        vector<PseudoJet> FourP_1;

        for (int i = 0; i < csize; i++)
        {
          if ((constit[i].user_index() - 22) != 0)
            Check_photon_jet = Check_photon_jet + 1;
        }
        if (Check_photon_jet == 0)
        {
          for (int i = 0; i < csize; i++)
          {
            //           cout << "constit_Photon jet:" << constit[i].user_index() << endl;
            continue;
          }
        }

        for (int i = 0; i < csize; i++)
        {
          fastjet::PseudoJet constituent(constit[i].px(), constit[i].py(), constit[i].pz(), constit[i].e());
          TLorentzVector constit_vec;
          constit_vec.SetPxPyPzE(constit[i].px(), constit[i].py(), constit[i].pz(), constit[i].e());
          int it;
          it = find(Total_particle_kind.begin(), Total_particle_kind.end(), abs(constit[i].user_index()))[0];
          if (it != abs(constit[i].user_index()))
          {
            Total_particle_kind.push_back(abs(constit[i].user_index()));
          }
          //
          for (int m = 0; m < Total_particle_kind.size(); m++)
          {
            //            cout << "[m]: "<< abs(Total_particle_kind[m]) << endl;
            if (abs(constit[i].user_index()) == Total_particle_kind[m])
              Total_particle_ID_no_cut->Fill(m);
            //      cout << " Total_particle_ID_no_cut->GetBinContent(m): " << Total_particle_ID_no_cut->GetBinContent(m+1) << endl;
          }
        }

        Eta_plot->Fill(p_using.Eta());
        if (abs(p_using.Eta()) > 0.6)
        {
          cout << "Particles of jet outside Eta==1" << endl;
          continue;
        }
        Eta_plot_after_cut->Fill(p_using.Eta());

        //      if(Check_Forth_And_Back_Bool[0]==1 and p_using.DeltaR(Forth_And_Back_Vector[0])<0.1*check)Forth_jet = Forth_jet+1;
        //     if(Check_Forth_And_Back_Bool[1]==1 and p_using.DeltaR(Forth_And_Back_Vector[1])<0.1*check)Back_jet = Back_jet+1;

        // fill jet substructure
        p.SetParameter(EffectiveRadius(sjets_truth[k], sjets_truth[k].constituents(), Rparam));  // 0
        p.SetParameter(nsubjettiness(sjets_truth[k], sjets_truth[k].constituents(), 1, Rparam)); // 1
        p.SetParameter(nsubjettiness(sjets_truth[k], sjets_truth[k].constituents(), 2, Rparam)); // 2
        p.SetParameter(nsubjettiness(sjets_truth[k], sjets_truth[k].constituents(), 3, Rparam)); //  3
        p.SetParameter(splittingscale(sjets_truth[k]));                                          // 4
        p.SetParameter(eccentricity(sjets_truth[k], sjets_truth[k].constituents()));             // 5
        truthjets.push_back(p);
        Truthjets_axis.push_back(p_using);
        //}

        for (int i = 0; i < csize; i++)
        {
          fastjet::PseudoJet constituent(constit[i].px(), constit[i].py(), constit[i].pz(), constit[i].e());
          TLorentzVector constit_vec;
          constit_vec.SetPxPyPzE(constit[i].px(), constit[i].py(), constit[i].pz(), constit[i].e());
          if (abs(constit_vec.Eta()) > 1)
          {
            Event_number_out_Eta2P1 = Event_number_out_Eta2P1 + 1;
            continue;
          }
          int it;
          it = find(Total_particle_kind.begin(), Total_particle_kind.end(), abs(constit[i].user_index()))[0];
          if (it != abs(constit[i].user_index()))
          {
            Total_particle_kind.push_back(abs(constit[i].user_index()));
          }
          for (int m = 0; m < Total_particle_kind.size(); m++)
          {
            if (abs(constit[i].user_index()) == Total_particle_kind[m])
              Total_particle_ID_eta_cut->Fill(m);
          }
        }

        //=========================================Cut and Find the information we want=================================//
        for (int i = 0; i < csize; i++)
        {
          fastjet::PseudoJet constituent(constit[i].px(), constit[i].py(), constit[i].pz(), constit[i].e());
          TLorentzVector constit_vec;
          constit_vec.SetPxPyPzE(constit[i].px(), constit[i].py(), constit[i].pz(), constit[i].e());
          int ID = 0;
          ID = find(PDG_with_no_charge.begin(), PDG_with_no_charge.end(), abs(constit[i].user_index()))[0];
          if (constit[i].perp() < 1.5 and ID != abs(constit[i].user_index()))
          { //cout << "Cut-off event" << endl;
            //cout << "constit[i].perp(): " << constit[i].perp()<< endl;
            //cout << "constit[i].getpdg(): "<< constit[i].user_index() << endl;
            continue;
          }
          if (abs(constit_vec.Eta()) > 1)
          {
            Event_number_out_Eta2P1 = Event_number_out_Eta2P1 + 1;
            continue;
          }

          int it;
          it = find(Total_particle_kind.begin(), Total_particle_kind.end(), abs(constit[i].user_index()))[0];
          if (it != abs(constit[i].user_index()))
          {
            Total_particle_kind.push_back(abs(constit[i].user_index()));
          }
          for (int m = 0; m < Total_particle_kind.size(); m++)
          {
            if (abs(constit[i].user_index()) == Total_particle_kind[m])
              Total_particle_ID_eta_PT_cut->Fill(m);
          }

          mass_average = mass_average + constit_vec.M();

          int ID1 = 0;
          ID1 = find(PDG_with_no_charge.begin(), PDG_with_no_charge.end(), abs(constit[i].user_index()))[0];

          if (constit[i].perp() < 1.5 and ID != abs(constit[i].user_index()))
          { //cout << "Cut-off event" << endl;
            //cout << "constit[i].perp(): " << constit[i].perp()<< endl;
            //cout << "constit[i].getpdg(): "<< constit[i].user_index() << endl;
            continue;
          }

          //  if(abs(constit_vec.Eta())>1){ Event_number_out_Eta2P1 = Event_number_out_Eta2P1 +1;  continue;}

          float constit_velocity = TMath::Power((TMath::Power(constit[i].px(), 2) + TMath::Power(constit[i].py(), 2) + TMath::Power(constit[i].pz(), 2)), 0.5) / constit[i].e(); //Beta
          float constit_velocity_vt = TMath::Power((TMath::Power(constit[i].px(), 2) + TMath::Power(constit[i].py(), 2)), 0.5) / constit[i].e();
          float constit_velocity_z = (constit[i].pz() / constit[i].e()); // Magnetic_consideration
          if (abs(sjets_truth[k].constituents()[i].user_index()) == 211)
          {
            check_Pion_DZ->Fill(2.3 / (TMath::Tan(constit_vec.Theta())));
            check_Pion_VZ->Fill(abs(constit_velocity_z));
            check_Pion_T->Fill(abs(2.3 * TMath::Power(10, 9) / (constit_velocity_z * SOL * (TMath::Tan(constit_vec.Theta())))));
          }
          if (abs(sjets_truth[k].constituents()[i].user_index()) == 2212)
          {
            check_Proton_DZ->Fill(2.3 / (TMath::Tan(constit_vec.Theta())));
            check_Proton_V->Fill(abs(constit_velocity));
            check_Proton_T->Fill(abs(2.3 * TMath::Power(10, 9) / (constit_velocity_z * SOL * (TMath::Tan(constit_vec.Theta())))));
          }
          if (abs(sjets_truth[k].constituents()[i].user_index()) != 22)
          {
            time_average = time_average + abs(2.3 * TMath::Power(10, 9) / (constit_velocity_z * SOL * (TMath::Tan(constit_vec.Theta())))); //[ns]
            jet_time.push_back(abs(2.3 * TMath::Power(10, 9) / (constit_velocity_z * SOL * (TMath::Tan(constit_vec.Theta())))));
            jet_time_sort.push_back(abs(2.3 * TMath::Power(10, 9) / (constit_velocity_z * SOL * (TMath::Tan(constit_vec.Theta())))));

            jet_time_for_rank_sort.push_back(abs(2.3 * TMath::Power(10, 9) / (constit_velocity_z * SOL * (TMath::Tan(constit_vec.Theta())))));
            jet_time_for_rank.push_back(abs(2.3 * TMath::Power(10, 9) / (constit_velocity_z * SOL * (TMath::Tan(constit_vec.Theta())))));
            jet_P_for_rank.push_back(constit_vec.P());
            jet_P_for_rank_sort.push_back(constit_vec.P());
            Rank_PDGID.push_back(sjets_truth[k].constituents()[i].user_index());

            velocity_jet_sort.push_back(constit_velocity_vt);
            velocity_jet.push_back(constit_velocity_vt);
            velocity_jet_Z.push_back(constit[i].pz() / constit[i].e());
            velocity_jet_Theta.push_back(constit_vec.Theta());
            if (constit_vec.Eta() == 0)
              cout << "Timing_eta_0: " << abs(2.3 * TMath::Power(10, 9) / (SOL * TMath::Sin(constit_vec.Theta()))) << endl;
            Timing_Standard->Fill(abs(2.3 * TMath::Power(10, 9) / (SOL * TMath::Sin(constit_vec.Theta())))); //Suppose all of them are photons.
            PT_jet.push_back(constit[i].perp());
            PT_jet_sort.push_back(constit[i].perp());
            momentum_jet.push_back(constit_vec.P());
            P_jet_sort.push_back(constit_vec.P());
            constit_PDG.push_back(abs(sjets_truth[k].constituents()[i].user_index()));
            FourP.push_back(constit_vec);
            FourP_1.push_back(constituent);
            event_number = event_number + 1;
          }
        }
        cout << "Jet_each_event: " << Jet_each_event << endl;
        Event_number_check_jet->Fill(Jet_each_event);
        //close the truth-loop

        if (event_number == 0)
          continue;
        cout << "truth-5: ";
        check_jet_particle_number->Fill(jet_time_for_rank_sort.size());
        if (event_number > 0 and Event_number_out_Eta2P1 > 0)
        {
          //cout << "Event_number_out_Eta2P1: " << Event_number_out_Eta2P1 << endl;
          //cout << "event_number: " << (event_number+Event_number_out_Eta2P1) << endl;
        }
        if ((Event_number_out_Eta2P1 / (event_number + Event_number_out_Eta2P1)) != 0)
        {
          //cout << "Out-of_Eta2P1_fraction:" << (Event_number_out_Eta2P1/(event_number+Event_number_out_Eta2P1)) << endl;
          //cout << "What the fucking unexpected events" << endl;
        }
        mass_average = mass_average / event_number;
        //cout << "mass_average: " << mass_average << endl;
        time_average = time_average / event_number;
        mass_sum_average->Fill(mass_average);
        double max_time = *max_element(jet_time.begin(), jet_time.end());
        double min_time = *min_element(jet_time.begin(), jet_time.end());
        double max_perp = *max_element(PT_jet.begin(), PT_jet.end());
        double min_perp = *min_element(PT_jet.begin(), PT_jet.end());

        sort(PT_jet_sort.begin(), PT_jet_sort.end());
        sort(jet_time_sort.begin(), jet_time_sort.end());
        sort(velocity_jet_sort.begin(), velocity_jet_sort.end());
        sort(P_jet_sort.begin(), P_jet_sort.end());
        sort(jet_time_for_rank_sort.begin(), jet_time_for_rank_sort.end());
        sort(jet_P_for_rank_sort.begin(), jet_P_for_rank_sort.end());
        int Trailing_ID_T = 0;          //One jet one trailing ID(T)
        int Trailing_ID_PT = 0;         //One jet one trailing ID(PT)
        int Next_to_trailing_ID_T = 0;  //One jet one trailing ID(T)
        int Next_to_trailing_ID_PT = 0; //One jet one trailing ID(PT)
        float Momentum_Trailing = 0;
        float Momentum_Next_to_Trailing = 0;
        float PT_Trailing = 0;
        float Theta_Leading = 0;
        float Theta_Trailing = 0;
        float Theta_Next_to_Trailing = 0;
        float Vz_Trailing = 0;
        float Vz_Next_to_Trailing = 0;
        float Vz_Leading = 0;
        vector<int> Particle_ID_T;
        vector<int> Particle_ID_T_Re;
        vector<int> Particle_ID_PT;
        vector<int> Particle_ID_PT_Re;
        vector<int> H_Particle_ID_T;
        vector<int> H_Particle_ID_PT;

        vector<float> Particle_ID_T_PT;
        vector<float> Particle_ID_T_PT_Re;
        vector<float> Particle_ID_T_T;
        vector<float> Particle_ID_T_T_Re;
        vector<float> Particle_ID_PT_T;
        vector<float> Particle_ID_PT_T_Re;
        vector<float> Particle_ID_PT_PT;
        vector<float> Particle_ID_PT_PT_Re;

        vector<float> dR_Highest_PT_T;
        vector<float> dR_Highest_PT_PT;
        vector<float> Timing_checking;
        vector<float> PT_checking;
        int check_timing_number = 0;
        int check_PT_number = 0;
        vector<TLorentzVector> HighestPT_Trailing_and_next_trailing;
        cout << "truth-6: ";
        //===============================Find_minimum_velocity_in_particle=========================//
        for (int i = 0; i < PT_jet.size(); i++)
        {
          if (max_perp == PT_jet[i])
          {
            HighestPT_Trailing_and_next_trailing.push_back(FourP[i]);
          }
        }
        //cout << "Highest(PT):" << endl; cout << "PDGID: "<< constit_PDG[i] << endl; cout << "PT_jet[i].pz()" << FourP_1[i].pz() << endl; cout << "PT_jet[i].px()" << FourP_1[i].px() << endl; cout << "PT_jet[i].py()" << FourP_1[i].py() << endl;}}
        cout << "truth121: " << endl;
        for (int j = 0; j < PT_jet.size(); j++)
        {
          for (int i = 0; i < PT_jet.size(); i++)
          {
            if (PT_jet_sort[j] == PT_jet[i])
            {
              PT_checking.push_back(PT_jet[i]);
              check_PT_number = check_PT_number + 1;
              Particle_ID_PT_PT.push_back(PT_jet[i]);
              Particle_ID_PT_T.push_back(jet_time[i]);
              //cout << "PT_jet[i]: " << PT_jet[i] << endl;
              Particle_ID_PT.push_back(constit_PDG[i]);
              dR_Highest_PT_PT.push_back(HighestPT_Trailing_and_next_trailing[0].DeltaR(FourP[i]));
              //cout << "PT_HighestPT_Trailing_and_next_trailing[0].DeltaR(FourP[i]): " << HighestPT_Trailing_and_next_trailing[0].DeltaR(FourP[i]) << endl;
              if (j < 5)
                h_Particles_dR_Highest_PT_PT[j]->Fill(HighestPT_Trailing_and_next_trailing[0].DeltaR(FourP[i]));
            }
          }
        }
        for (int j = 0; j < jet_time.size(); j++)
        {
          for (int i = 0; i < jet_time.size(); i++)
          {
            //if(jet_time_sort[jet_time.size()-1-j]==jet_time[i])
            if (velocity_jet_sort[j] == velocity_jet[i])
            {
              check_timing_number = check_timing_number + 1;
              Timing_checking.push_back(jet_time[i]);
              Particle_ID_T_PT.push_back(PT_jet[i]);
              Particle_ID_T_T.push_back(jet_time[i]);
              Particle_ID_T.push_back(constit_PDG[i]);
              dR_Highest_PT_T.push_back(HighestPT_Trailing_and_next_trailing[0].DeltaR(FourP[i]));
              //cout << "T_HighestPT_Trailing_and_next_trailing[0].DeltaR(FourP[i]): " << HighestPT_Trailing_and_next_trailing[0].DeltaR(FourP[i]) << endl;
              if (j < 5)
                h_Particles_dR_Highest_PT_T[j]->Fill(HighestPT_Trailing_and_next_trailing[0].DeltaR(FourP[i]));
            }
          }
        }
        //======================================================================================
        cout << "1: " << endl;

        if (PT_jet_sort.size() > 0)
        {
          h_Jet_SM_PT_PT->Fill(TMath::Log10(Particle_ID_PT_PT[0]));
          h_Jet_SM_PT_T->Fill(Particle_ID_PT_T[0]);
          h_Jet_T_PT->Fill(TMath::Log10(Particle_ID_T_PT[0]));
          h_Jet_T_T->Fill(Particle_ID_T_T[0]);

          for (int joke = 0; joke < PT_jet_sort.size(); joke++)
          {
            int Check = 0;
            for (int joke_1 = 0; joke_1 < PT_jet_sort.size(); joke_1++)
            {
              if (PT_jet_sort[PT_jet_sort.size() - 1 - joke] == PT_jet[joke_1])
              {
                int ID3 = 0;
                ID3 = find(PDG_with_no_charge.begin(), PDG_with_no_charge.end(), abs(constit_PDG[joke_1]))[0];
                if (ID3 != abs(constit_PDG[joke_1]))
                {
                  //cout << "PT_jet_sort[PT_jet_sort.size()-1-joke]/Jet_PT: " << PT_jet_sort[PT_jet_sort.size()-1-joke]/Jet_PT << endl;
                  h_Jet_PT_HI_PT_C_P->Fill(PT_jet_sort[PT_jet_sort.size() - 1 - joke] / Jet_PT);
                  //cout << "2: " << endl;
                  Check = Check + 1;
                  break;
                }
                else
                {
                  continue;
                }
              }
            }
            if (Check == 1)
              break;
          }
        }
        cout << "3: " << endl;
        //
        int Num_of_Tra_pT = 0;

        for (int j = 0; j < jet_time.size(); j++)
        {
          if ((event_number - 1) < j)
            continue;
          else
          {
            for (int m = 0; m < Trailing_particle_kind_limit_pT.size(); m++)
            {
              if (abs(Particle_ID_PT[j]) == Trailing_particle_kind_limit_pT[m] and abs(Particle_ID_PT[j]) != 22 and Num_of_Tra_pT < 5)
              {
                Num_of_Tra_pT = Num_of_Tra_pT + 1;
                cout << "Input TMath::Log10(Particle_ID_PT_PT[j]):: " << TMath::Log10(Particle_ID_PT_PT[j]) << endl;
                cout << "Input (Particle_ID_PT_PT[j]):: " << (Particle_ID_PT_PT[j]) << endl;
                Particle_ID_PT_PT_Re.push_back((Particle_ID_PT_PT[j]));
                Particle_ID_PT_T_Re.push_back(Particle_ID_PT_T[j]);
                Particle_ID_PT_Re.push_back(Particle_ID_PT[j]);
              }
            }
          }
        }
        if (Num_of_Tra_pT != 5)
          continue;
        int Num_of_Tra_V = 0;
        cout << "5: " << endl;
        for (int j = 0; j < jet_time.size(); j++)
        {
          cout << "j: " << j << endl;
          if ((event_number - 1) < j)
            continue;
          else
          {
            if ((Particle_ID_T_PT[j]) == Particle_ID_PT_PT_Re[0] or (Particle_ID_T_PT[j]) == Particle_ID_PT_PT_Re[1] or (Particle_ID_T_PT[j]) == Particle_ID_PT_PT_Re[2] or (Particle_ID_T_PT[j]) == Particle_ID_PT_PT_Re[3] or (Particle_ID_T_PT[j]) == Particle_ID_PT_PT_Re[4])
            {
              cout << "??? " << endl;
              cout << "Overlap Output TMath::Log10(Particle_ID_T_PT[j]): " << TMath::Log10(Particle_ID_T_PT[j]) << endl;
              continue;
            }
            else
            {
              for (int m = 0; m < Trailing_particle_kind_limit.size(); m++)
              {
                if (abs(Particle_ID_T[j]) == Trailing_particle_kind_limit[m] and abs(Particle_ID_T[j]) != 22 and Num_of_Tra_V < 5)
                {
                  cout << "Used_j: " << j << endl;
                  cout << "Output (Particle_ID_T_PT[j]): " << (Particle_ID_T_PT[j]) << endl;
                  cout << "Output TMath::Log10(Particle_ID_T_PT[j]): " << TMath::Log10(Particle_ID_T_PT[j]) << endl;
                  Num_of_Tra_V = Num_of_Tra_V + 1;
                  Particle_ID_T_PT_Re.push_back((Particle_ID_T_PT[j]));
                  Particle_ID_T_T_Re.push_back(Particle_ID_T_T[j]);
                  Particle_ID_T_Re.push_back(Particle_ID_T[j]);
                }
              }
            }
          }
        }
        cout << "Num_of_Tra_pT: " << Num_of_Tra_pT << "Num_of_Tra_V: " << Num_of_Tra_V << endl;
        if (Num_of_Tra_V != 5)
          continue;
        //Write the codes for checking both of the cases containing the order of the trailing particle is up to fifth.

        for (int j = 0; j < 5; j++)
        {
          cout << "Particle_ID_PT_PT_Re: " << Particle_ID_PT_PT_Re[j] << endl;
          cout << "TMath::Log10(Particle_ID_PT_PT_Re: " << TMath::Log10(Particle_ID_PT_PT_Re[j]) << endl;
        }
        for (int j = 0; j < 5; j++)
        {
          cout << "Particle_ID_T_PT_Re: " << Particle_ID_T_PT_Re[j] << endl;
          cout << "TMath::Log10(Particle_ID_T_PT_Re: " << TMath::Log10(Particle_ID_T_PT_Re[j]) << endl;
        }
        cout << "7: " << endl;

        for (int j = 0; j < 5; j++)
        {
          if ((event_number - 1) < j)
            continue;
          else
          {
            /*
                int it2;
                it2=find(Trailing_particle_kind.begin(),Trailing_particle_kind.end(),abs(Particle_ID_PT[j]))[0];
                if(it2!=abs(Particle_ID_PT[j]))
                {        
                Trailing_particle_kind.push_back(abs(Particle_ID_PT[j]));
                }
		*/
            for (int m = 0; m < Trailing_particle_kind_limit_pT.size(); m++)
            {
              if (abs(Particle_ID_PT_Re[j]) == Trailing_particle_kind_limit_pT[m])
              {
                H_Particle_ID_PT.push_back(m);
                h_Particles_Rank_PT[j]->Fill(m);
                h_Particles_Rank_PT_vs_T[j]->Fill(m, Particle_ID_PT_T_Re[j]);
                if (TMath::Log10(Particle_ID_PT_PT[j]) > -1.5)
                  h_Particles_Rank_PT_vs_PT[j]->Fill(m, TMath::Log10(Particle_ID_PT_PT_Re[j]));
                if (TMath::Log10(Particle_ID_PT_PT[j]) < -1.5)
                  h_Particles_Rank_PT_vs_PT[j]->Fill(m, -1.499);
              }
            }
          }
        }
        for (int j = 0; j < 5; j++)
        {
          //cout << "j: " << j << endl;
          if ((event_number - 1) < j)
            continue;
          else
          {
            /*
        	int it;
        	it=find(Trailing_particle_kind.begin(),Trailing_particle_kind.end(),abs(Particle_ID_T[j]))[0];
        	if(it!=abs(Particle_ID_T[j])) 
        	{       
        	Trailing_particle_kind.push_back(abs(Particle_ID_T[j]));
        	}
		*/
            for (int m = 0; m < Trailing_particle_kind_limit.size(); m++)
            {

              if (abs(Particle_ID_T_Re[j]) == Trailing_particle_kind_limit[m])
              {
                H_Particle_ID_T.push_back(m);
                h_Particles_Rank_T[j]->Fill(m);
                h_Particles_Rank_T_vs_T[j]->Fill(m, Particle_ID_T_T_Re[j]);
                if (TMath::Log10(Particle_ID_T_PT[j]) > -1.5)
                  h_Particles_Rank_T_vs_PT[j]->Fill(m, TMath::Log10(Particle_ID_T_PT_Re[j]));
                if (TMath::Log10(Particle_ID_T_PT[j]) < -1.5)
                  h_Particles_Rank_T_vs_PT[j]->Fill(m, -1.499);
              }
            }
          }
        }
        cout << "truth131: " << endl;
        if (event_number >= 1)
        {
          PT_Tr0T_HPt = TMath::Log10(Particle_ID_T_PT_Re[0]);
          PT_Tr0PT_HPt = TMath::Log10(Particle_ID_PT_PT_Re[0]);
        }
        if (event_number >= 2)
        {
          PT_Tr1T_HPt = TMath::Log10(Particle_ID_T_PT_Re[1]);
          PT_Tr1PT_HPt = TMath::Log10(Particle_ID_PT_PT_Re[1]);
        }
        if (event_number >= 3)
        {
          PT_Tr2T_HPt = TMath::Log10(Particle_ID_T_PT_Re[2]);
          PT_Tr2PT_HPt = TMath::Log10(Particle_ID_PT_PT_Re[2]);
        }
        if (event_number >= 4)
        {
          PT_Tr3T_HPt = TMath::Log10(Particle_ID_T_PT_Re[3]);
          PT_Tr3PT_HPt = TMath::Log10(Particle_ID_PT_PT_Re[3]);
        }
        if (event_number >= 5)
        {
          PT_Tr4T_HPt = TMath::Log10(Particle_ID_T_PT_Re[4]);
          PT_Tr4PT_HPt = TMath::Log10(Particle_ID_PT_PT_Re[4]);
        }

        cout << "truth-7: ";
        for (int i = 0; i < jet_time.size(); i++)
        {
          if (jet_time_sort[jet_time.size() - 1] == jet_time[i])
          {
            Trailing_ID_T = constit_PDG[i];
          }
          if (jet_time_sort[jet_time.size() - 2] == jet_time[i])
          {
            Next_to_trailing_ID_T = constit_PDG[i];
          }
          if (PT_jet_sort[0] == PT_jet[i])
          {
            Trailing_ID_PT = constit_PDG[i];
          }
          if (PT_jet_sort[1] == PT_jet[i])
          {
            Next_to_trailing_ID_PT = constit_PDG[i];
          }
        }

        int it;
        it = find(Trailing_particle_kind.begin(), Trailing_particle_kind.end(), abs(Trailing_ID_T))[0];
        if (it != abs(Trailing_ID_T))
        {
          Trailing_particle_kind.push_back(abs(Trailing_ID_T));
        }
        else
          cout << "" << endl; //

        for (int m = 0; m < Trailing_particle_kind.size(); m++)
        {
          //cout << "Trailing_particle_kind[m]: "<< abs(Trailing_particle_kind[m]) << endl;
          if (abs(Trailing_ID_T) == Trailing_particle_kind[m] and abs(Trailing_ID_T) != 22)
            Trailing_particle_ID_T->Fill(m);
          //cout << "Trailing_particle_ID_T->GetBinContent(m): " << Trailing_particle_ID_T->GetBinContent(m+1) << endl;
        }

        int it2;
        it2 = find(Trailing_particle_kind.begin(), Trailing_particle_kind.end(), abs(Trailing_ID_PT))[0];
        if (it2 != abs(Trailing_ID_PT))
        {
          Trailing_particle_kind.push_back(abs(Trailing_ID_PT));
        }
        else
          cout << "" << endl; //

        for (int m = 0; m < Trailing_particle_kind.size(); m++)
        {
          //cout << "Trailing_particle_kind[m]: "<< abs(Trailing_particle_kind[m]) << endl;
          if (abs(Trailing_ID_PT) == Trailing_particle_kind[m] and abs(Trailing_ID_PT) != 22)
            Trailing_particle_ID_PT->Fill(m);
          //cout << "Trailing_particle_ID_PT->GetBinContent(m): " << Trailing_particle_ID_PT->GetBinContent(m+1) << endl;
        }

        int it4;
        it4 = find(Trailing_particle_kind.begin(), Trailing_particle_kind.end(), abs(Next_to_trailing_ID_T))[0];
        if (it4 != abs(Next_to_trailing_ID_T))
        {
          Trailing_particle_kind.push_back(abs(Next_to_trailing_ID_T));
        }
        else
          cout << "" << endl; //

        for (int m = 0; m < Trailing_particle_kind.size(); m++)
        {
          //cout << "Trailing_particle_kind[m]: "<< abs(Trailing_particle_kind[m]) << endl;
          if (abs(Next_to_trailing_ID_T) == Trailing_particle_kind[m] and abs(Next_to_trailing_ID_T) != 22)
            Next_to_trailing_particle_ID_T->Fill(m);
          //cout << "Next_to_trailing_particle_ID_T->GetBinContent(m): " << Next_to_trailing_particle_ID_T->GetBinContent(m+1) << endl;
        }

        int it3;
        it3 = find(Trailing_particle_kind.begin(), Trailing_particle_kind.end(), abs(Next_to_trailing_ID_PT))[0];
        if (it3 != abs(Next_to_trailing_ID_PT))
        {
          Trailing_particle_kind.push_back(abs(Next_to_trailing_ID_PT));
        }
        else
          cout << "" << endl; //

        for (int m = 0; m < Trailing_particle_kind.size(); m++)
        {
          //cout << "Trailing_particle_kind[m]: "<< abs(Trailing_particle_kind[m]) << endl;
          if (abs(Next_to_trailing_ID_PT) == Trailing_particle_kind[m] and abs(Next_to_trailing_ID_PT) != 22)
            Next_to_trailing_particle_ID_PT->Fill(m);
          //cout << "Next_to_trailing_particle_ID_PT->GetBinContent(m): " << Next_to_trailing_particle_ID_PT->GetBinContent(m+1) << endl;
        }

        //=================================================================================================================================//
        //if(jet_time_sort[0]<jet_time_sort[1] and jet_time_sort[1]<jet_time_sort[2]) cout << "Let go party party all night oh oh!~" << endl;

        //cout << "jet_time_for_rank_sort.size(): " << jet_time_for_rank_sort.size() << endl;

        int event_checkk = 0;
        for (int j = 0; j < jet_time_for_rank_sort.size(); j++)
        {
          for (int i = 0; i < jet_time_for_rank.size(); i++)
          {
            if (jet_time_for_rank_sort[(jet_time_for_rank_sort.size() - 1) - j] == jet_time_for_rank[i])
            {
              for (int kk = 0; kk < jet_P_for_rank.size(); kk++)
              {
                if (jet_P_for_rank[i] == jet_P_for_rank_sort[kk])
                {
                  Timing_momentum_correlation->Fill(float((j + 1)) / float((jet_time_for_rank_sort.size())), float((kk + 1)) / float((jet_time_for_rank_sort.size())));
                  //	cout << "float((j+1))/float((jet_time_for_rank_sort.size())): " << float((j+1))/float((jet_time_for_rank_sort.size())) << endl;
                  //	cout << "float((kk+1))/float((jet_time_for_rank_sort.size())): " << float((kk+1))/float((jet_time_for_rank_sort.size())) << endl;
                  Timing_P_rank_difference_momentum_correlation->Fill(TMath::Log10(jet_P_for_rank[kk]), float(j - kk) / float((jet_time_for_rank_sort.size())));
                  //	cout << "float(j-kk)/float((jet_time_for_rank_sort.size())): " << float(j-kk)/float((jet_time_for_rank_sort.size())) << endl;
                  //						cout << "TMath::Log10(jet_P_for_rank[kk]): " << TMath::Log10(jet_P_for_rank[kk]) << endl;
                  //cout << "jet_P_for_rank_sort[kk]: "<< jet_P_for_rank_sort[kk] << endl;
                  //								cout << "(j+1): " << (j+1) << "(kk+1): " << (kk+1) << endl ;
                  //cout << "j-k: " << j-k << endl;
                  event_checkk = event_checkk + 1;
                }
                else
                {
                  continue;
                }
              }
            }
            else
            {
              continue;
            }
          }
        }
        //cout << "event_checkk: " << event_checkk << endl;
        // vector<TLorentzVector> HighestPT_Trailing_and_next_trailing;
        //=====
        //=====
        for (int i = 0; i < constit_PDG.size(); i++)
        {
          if (constit_PDG[i] == 2212)
          {
            //			cout << "Great!" << endl;
            Timing_detector_dR_Leading_Proton_PT->Fill(HighestPT_Trailing_and_next_trailing[0].DeltaR(FourP[i]));
            //			cout << "HighestPT_Trailing_and_next_trailing[0].DeltaR(FourP[i]): " << HighestPT_Trailing_and_next_trailing[0].DeltaR(FourP[i]) << endl;
          }
        }
        //=====
        for (int i = 0; i < jet_time.size(); i++)
        {
          if (jet_time_sort[0] == jet_time[i])
          {
            Vz_Leading = velocity_jet_Z[i];
            Theta_Leading = velocity_jet_Theta[i];
          }
        }
        //=====
        for (int i = 0; i < jet_time.size(); i++)
        {
          if (jet_time_sort[jet_time.size() - 1] == jet_time[i])
          {
            Theta_Trailing = velocity_jet_Theta[i];
            Vz_Trailing = velocity_jet_Z[i];
            Momentum_Trailing = momentum_jet[i];
            PT_Trailing = PT_jet[i];
            HighestPT_Trailing_and_next_trailing.push_back(FourP[i]);
          }
        }
        //cout << "Trailing: " << endl; cout << "PDGID: "<< constit_PDG[i] << endl;cout << "PT_jet[i].e()" << FourP_1[i].e() << endl; cout << "PT_jet[i].pz()" << FourP_1[i].pz() << endl; cout << "PT_jet[i].px()" << FourP_1[i].px() << endl; cout << "PT_jet[i].py()" << FourP_1[i].py() << endl;}}
        //======
        for (int i = 0; i < jet_time.size(); i++)
        {
          if (jet_time_sort[jet_time.size() - 2] == jet_time[i])
          {
            Theta_Next_to_Trailing = velocity_jet_Theta[i];
            Vz_Next_to_Trailing = velocity_jet_Z[i];
            Momentum_Next_to_Trailing = momentum_jet[i];
            HighestPT_Trailing_and_next_trailing.push_back(FourP[i]);
          }
        }
        //cout << "Next-to-Trailing: " << endl;cout << "PDGID: "<< constit_PDG[i] << endl;cout << "PT_jet[i].pz()" << FourP_1[i].pz() << endl; cout << "PT_jet[i].px()" << FourP_1[i].px() << endl; cout << "PT_jet[i].py()" << FourP_1[i].py() << endl;cout << "PT_jet[i].e()" << FourP_1[i].e() << endl;}}

        for (int i = 0; i < PT_jet.size(); i++)
        {
          if (PT_jet_sort[0] == PT_jet[i])
          {
            HighestPT_Trailing_and_next_trailing.push_back(FourP[i]);
          }
        }
        for (int i = 0; i < PT_jet.size(); i++)
        {
          if (PT_jet_sort[1] == PT_jet[i])
          {
            HighestPT_Trailing_and_next_trailing.push_back(FourP[i]);
          }
        }

        //if(PT_Trailing<1.5) cout << "This is the PT<1.5 paticle: " << Trailing_ID_PT << endl;
        //if(HighestPT_Trailing_and_next_trailing.size()>5) cout << "Not Weird! The number of the trailing and next-trailing" << endl;

        // cout << "Momentum_Trailing: " << Momentum_Trailing << endl;
        // cout << "Momentum_Next_to_Trailing: " << Momentum_Next_to_Trailing << endl;
        // cout << "Highest_PT_trailing_dR_T: " << HighestPT_Trailing_and_next_trailing[0].DeltaR(HighestPT_Trailing_and_next_trailing[1]) << endl;
        //cout << "Highest_PT_next_to_trailing_dR_T: " << HighestPT_Trailing_and_next_trailing[0].DeltaR(HighestPT_Trailing_and_next_trailing[2]) << endl;
        // cout << "Highest_PT_trailing_dR_PT: " << HighestPT_Trailing_and_next_trailing[0].DeltaR(HighestPT_Trailing_and_next_trailing[3]) << endl;
        //cout << "Highest_PT_next_to_trailing_dR_PT: " << HighestPT_Trailing_and_next_trailing[0].DeltaR(HighestPT_Trailing_and_next_trailing[4]) << endl;
        //	  cout << "Vz_Trailing: " << Vz_Trailing << "Vz_Next_to_Trailing: " << Vz_Next_to_Trailing << endl;
        //	 cout << "TMath::Tan(Theta_Trailing): " << TMath::Tan(Theta_Trailing) << "TMath::Tan(Theta_Next_to_Trailing): " << TMath::Tan(Theta_Next_to_Trailing) << endl;
        //	 cout << "Theta_Trailing: " << Theta_Trailing << "Theta_Next_to_Trailing: " << Theta_Next_to_Trailing << endl;
        Timing_detector_Average->Fill(abs(time_average));
        Timing_detector_Leading->Fill(abs(2.3 * TMath::Power(10, 9) / (Vz_Leading * SOL * TMath::Tan(Theta_Leading))));
        Timing_detector_Trailing->Fill(abs(2.3 * TMath::Power(10, 9) / (Vz_Trailing * SOL * TMath::Tan(Theta_Trailing))));
        Timing_detector_next_to_trailing->Fill(abs(2.3 * TMath::Power(10, 9) / (Vz_Next_to_Trailing * SOL * TMath::Tan(Theta_Next_to_Trailing))));
        Timing_detector_Trailing_P->Fill(abs(Momentum_Trailing));
        Timing_detector_next_to_trailing_P->Fill(abs(Momentum_Next_to_Trailing));
        Timing_detector_Trailing_V->Fill(TMath::Log10(3 * TMath::Power(10, 8) * abs(velocity_jet_sort[0])));
        cout << "Trailing-V: " << TMath::Log10(3 * TMath::Power(10, 8) * abs(velocity_jet_sort[0])) << endl;
        Timing_detector_next_to_trailing_V->Fill(abs(velocity_jet_sort[1]));
        Timing_detector_dR_Leading_trailing_T->Fill(HighestPT_Trailing_and_next_trailing[0].DeltaR(HighestPT_Trailing_and_next_trailing[1]));
        Timing_detector_dR_Leading_next_trailing_T->Fill(HighestPT_Trailing_and_next_trailing[0].DeltaR(HighestPT_Trailing_and_next_trailing[2]));
        Timing_detector_dR_Leading_trailing_PT->Fill(HighestPT_Trailing_and_next_trailing[0].DeltaR(HighestPT_Trailing_and_next_trailing[3]));
        Timing_detector_dR_Leading_next_trailing_PT->Fill(HighestPT_Trailing_and_next_trailing[0].DeltaR(HighestPT_Trailing_and_next_trailing[4]));
        //	cout << " Timing_detector_Average: "<< time_average << "Timing_detector_Trailing: "<< abs(2.3*TMath::Power(10,9)/(Vz_Trailing*SOL*TMath::Tan(Theta_Trailing)))  << "Timing_detector_next_to_trailing: " << abs(2.3*TMath::Power(10,9)/(Vz_Next_to_Trailing*SOL*TMath::Tan(Theta_Next_to_Trailing))) ;
        //	cout << "TIming_detector_Leading: " << abs(2.3*TMath::Power(10,9)/(Vz_Leading*SOL*TMath::Tan(Theta_Leading))) << endl;

        velocity_jet.clear();
        Timing_detector_Average_tem->Clear();
        if (pt >= 10000)
        {
          for (int i = 0; i < csize; i++)
          {
            // std::cout << "Truth Jets const.Eti20(): " << (constit[i].Et()) << std::endl;
            //            h_truth_jets_const_Et10->Fill(constit[i].Et());
          }
        }
      }

      // includes Geant4
      /*
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

              //TLorentzVector p;
              //p.SetPxPyPzE(px,py,pz,e);
              if ( pt < ETmin)                    continue;
              if ( fabs(eta)> ETAmax )            continue;
              LParticle p( sjets_truth_sim[k].px(), sjets_truth_sim[k].py(), sjets_truth_sim[k].pz(),  sjets_truth_sim[k].e(),0);
              vector<PseudoJet> constit=sjets_truth_sim[k].constituents();
              int csize=constit.size();
                  for (int i=0; i<csize; i++) {
                  h_jet_econst_truth_sim->Fill(constit[i].e(), constit[i].e());
                  h_jet_econst_truth_sim_frac->Fill(TMath::Log10(constit[i].e()), constit[i].e()/e);
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
   h_jetjet_m_truth->Fill( LL.M());
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
   h_jet_pt_truth->Fill(pt);
   h_jet_m_truth->Fill(mass);
 
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
  IMPL::LCCollectionVec* col2 = (IMPL::LCCollectionVec*) evt->getCollection( "PandoraPFOCollection"  ) ;
  int nPFO = col2->getNumberOfElements() ;
    for(int i=0 ; i<nPFO ; ++i){
      EVENT::ReconstructedParticle* mcp =  (EVENT::ReconstructedParticle*) col2->getElementAt(i) ;
      double px = mcp->getMomentum()[0];
      double py = mcp->getMomentum()[1];
      double pz = mcp->getMomentum()[2];
      double m = 0; // mcp->getMomentum()[3];
      double e=sqrt(px*px+py*py+pz*pz+m*m);

      PseudoJet pp(px,py,pz,e);
      double eta_r=pp.pseudorapidity();
      double phi_r=pp.phi();
      double pt_r=pp.pt();
      // fill clusters 
      h_pt_pfa->Fill(pt_r);
      h_eta_pfa->Fill(eta_r);


      if (pp.pt()>minPtConst)avec_pfo.push_back( pp );
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
              if ( pt < ETmin)                    continue;
              if ( fabs(eta)> ETAmax )            continue;
              LParticle p( sjets_pfo[k].px(),sjets_pfo[k].py(),sjets_pfo[k].pz(),sjets_pfo[k].e(),0);
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
   h_jetjet_m_pfo->Fill( LL.M());
   }



  //tracks 
  // look up at: /share/sl6/ilcsoft/slic/release-v05-00-00/slicPandora/HEAD/lcio/v02-04-03/build/include/EVENT

  IMPL::LCCollectionVec* col3 = (IMPL::LCCollectionVec*) evt->getCollection( "Tracks"  ) ;
  int nTRK = col3->getNumberOfElements() ;
    for(int i=0 ; i<nTRK ; ++i){
      EVENT::Track* mcp =  (EVENT::Track*) col3->getElementAt(i) ;
      //float* pos= col3->getPosition();
      //px = mcp->getMomentum()[0] ;
      //py = mcp->getMomentum()[1] ;
      //pz = mcp->getMomentum()[2] ;
  }



  double calo_sum=0;
  // clusters
  vector<PseudoJet> avec_clus;
  double xsum_cl=0;
  IMPL::LCCollectionVec* col5 = (IMPL::LCCollectionVec*) evt->getCollection("ReconClusters") ;
  int nCL = col5->getNumberOfElements() ;
   for(int i=0 ; i<nCL ; ++i){
    EVENT::Cluster* mcp =  (EVENT::Cluster*) col5->getElementAt(i) ;
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
    PseudoJet pj(px,py,pz,e);
    double eta_r=pj.pseudorapidity();
    double phi_r=pj.phi();
    double pt_r=pj.pt();
     // fill clusters 
    h_pt_clus->Fill(pt_r);
    h_eta_clus->Fill(eta_r);

    //cout << " e=" << e <<  " phi=" << pj.phi() << " eta=" << pj.eta() << endl;
    if (pt_r>minPtConst) avec_clus.push_back( pj );

  }


  // cout << "Calo clus sum=" << calo_sum << endl;


*/

      //====Calorimeter1

      /*
===comment
if(Truthjets_axis.size()==0) continue;
 // HCAL simulated raw hits
  double hcalsum_raw=0;

  vector<PseudoJet> avec_hits_raw_sf;
  vector<LParticle> Calhits;
  vector<LParticle> simhits;
  vector<LParticle> simhits_1;

  IMPL::LCCollectionVec* col50_1 = (IMPL::LCCollectionVec*) evt->getCollection("HAD_BARREL") ;
  int nCL11 = col50_1->getNumberOfElements() ;
  int check_nCL11=0;
  cout << "nCL11: " << nCL11 ;
  for(int i=0 ; i<nCL11 ; ++i){
    EVENT::CalorimeterHit* mcp_1 =  (EVENT::CalorimeterHit*) col50_1->getElementAt(i) ;
    int cellId0 = mcp_1->getCellID0();
    int cellId1 = mcp_1->getCellID1();
    long long cellId = ((long long)cellId1) << 32 | cellId0;
    int layer = decoder->getFieldValue("layer", cellId);
    if(layer>20) continue; 
    check_nCL11 = check_nCL11 + 1;
    const float* pos= mcp_1->getPosition();
    float x=pos[0];
    float y=pos[1];
    float z=pos[2];
    //cout << "xyzCal: " << x << " " << y << " " << z << " " << endl;
    double e = mcp_1->getEnergy();
    double _tmp = std::sqrt(x*x + y*y + z*z);
    double px =  e*x/_tmp;
    double py =  e*y/_tmp;
    double pz =  e*z/_tmp;
    PseudoJet pj_sf(px,py,pz,e);
    LParticle p(px,py,pz,e,layer);
    p.SetParameter( x*1000 );
    p.SetParameter( y*1000 );
    p.SetParameter( z*1000 );
        if(e>0.5)   {avec_hits_raw_sf.push_back(pj_sf);
		    //Calhits.push_back(p);		
						}
        }
  IMPL::LCCollectionVec* col50_2 = (IMPL::LCCollectionVec*) evt->getCollection("EM_BARREL") ;
  int nCL12 = col50_2->getNumberOfElements() ;
  cout << "nCL12: " << nCL12 ;
  for(int i=0 ; i<nCL12 ; ++i){
        EVENT::CalorimeterHit* mcp_1 =  (EVENT::CalorimeterHit*) col50_2->getElementAt(i) ;
    const float* pos= mcp_1->getPosition();
    float x=pos[0];
    float y=pos[1];
    float z=pos[2];
    double e = mcp_1->getEnergy();
    double _tmp = std::sqrt(x*x + y*y + z*z);
    double px =  e*x/_tmp;
    double py =  e*y/_tmp;
    double pz =  e*z/_tmp;
    int cellId0 = mcp_1->getCellID0();
    int cellId1 = mcp_1->getCellID1();
    long long cellId = ((long long)cellId1) << 32 | cellId0;
    int layer = decoder_ecal->getFieldValue("layer", cellId);
    LParticle p(px,py,pz,e,layer);
    PseudoJet pj_sf(px,py,pz,e);
    p.SetParameter( x*1000 );
    p.SetParameter( y*1000 );
    p.SetParameter( z*1000 );
    p.SetParameter( layer ) ;
       if(e>0.5) {
		   //avec_hits_raw_sf.push_back(pj_sf);
		   Calhits.push_back(p);
	   	     }
							
        }
cout << "33:";
====Comment===
*/
      /*
  int check_cell=0;
  IMPL::LCCollectionVec* col50 = (IMPL::LCCollectionVec*) evt->getCollection("HcalBarrelHits") ;
  int nCL = col50->getNumberOfElements() ;
   for(int i=0 ; i<nCL ; ++i){
    check_cell = check_cell + 1;
        EVENT::SimCalorimeterHit* mcp =  (EVENT::SimCalorimeterHit*) col50->getElementAt(i) ;
    const float* pos= mcp->getPosition();
    float x=pos[0];
    float y=pos[1];
    float z=pos[2];
    double e = mcp->getEnergy();
    double Thit=mcp->getTimeCont(0);
       // cout << "xyzSim: " << x << " " << y << " " << z << " " << endl;
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
    
    //if(e>0.5) cout << "e: " << endl;
    double Rpos_cm=0.1*std::sqrt(x*x+y*y);
    double _tmp = std::sqrt(x*x + y*y + z*z);
    double px =  e*x/_tmp;
    double py =  e*y/_tmp;
    double pz =  e*z/_tmp;
    hcalsum_raw=hcalsum_raw+e;
    PseudoJet pj_sf(px,py,pz,e);
    //double eta_r=pj.pseudorapidity();
    //double phi_r=pj.phi();
    //double pt_r=pj.pt();
    //cout << " e=" << e <<  " phi=" << pj.phi() << " eta=" << pj.eta() << endl;

    // fill hits
     LParticle p(px,py,pz,e,layer);
     p.SetType(1); // HCAL 
     p.SetCharge(layer);  
     p.SetStatus(mcp->getNMCContributions());
     p.SetParameter( x  );
     p.SetParameter( y  );
     p.SetParameter( z  );
     p.SetParameter( layer_pos_cm ); 
	// find fastest hit
    float timeCont = mcp->getTimeCont(0);
    EVENT::MCParticle* pmm =mcp->getParticleCont(0); 
    int pdg=pmm->getPDG ();
    int status=pmm->getSimulatorStatus ();
    float rawTime = timeCont;
    int nCont=mcp->getNMCContributions();
    for (int jjj=0; jjj<nCont; jjj++) {
                  if ( mcp->getTimeCont(jjj) < rawTime )
                       rawTime  = mcp->getTimeCont(jjj);
                       EVENT::MCParticle* pmm =mcp->getParticleCont(jjj); 
                       pdg=pmm->getPDG ();
                       status=pmm->getSimulatorStatus();
                }

     p.SetParameter(rawTime); // fastest hit 
     p.SetParameter(avt);     // average hit time  
     p.SetParameter( (double)pdg  ); 
     p.SetParameter( (double)status  );
     p.SetParameter(  cellId0 );
     p.SetParameter(  cellId1 );
     

     // PDG of first constribution 
     if (mcp->getNMCContributions()>0){
         EVENT::MCParticle* pmm =mcp->getParticleCont(0); 
         int pdg=pmm->getPDG ();
         int status=pmm->getSimulatorStatus ();
         p.SetParameter( (double)pdg  ); 
         p.SetParameter( (double)status  );
         // p.SetParameter( (double)(mcp->getGeneratorStatus()));
     }



      //simhits.push_back(p);

     // cuts as in the default reconstruction
     if (e>0.0005) h_hits_time_abovecut->Fill(Thit,e);
 

 // corrected by sampling fraction 
    double HCAL_SF=0.031;
    e=e/HCAL_SF;
    px =  e*x/_tmp;
    py =  e*y/_tmp;
    pz =  e*z/_tmp;

    } // end fill of hits
*/
      //cout << " check_cell: " << check_cell << endl;
      //Calorimeter2
      double ecalsum_raw = 0;

      /*
===comment
// ECAL hits
  IMPL::LCCollectionVec* col53 = (IMPL::LCCollectionVec*) evt->getCollection("EcalBarrelHits") ;
  //IMPL::LCCollectionVec* col53 = (IMPL::LCCollectionVec*) evt->getCollection("EM_BARREL") ;
  int nCL1 = col53->getNumberOfElements() ;
   for(int i=0 ; i<nCL1 ; ++i){
     EVENT::SimCalorimeterHit* mcp =  (EVENT::SimCalorimeterHit*) col53->getElementAt(i) ;
     //EVENT::CalorimeterHit* mcp =  (EVENT::CalorimeterHit*) col53->getElementAt(i) ;

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
    PseudoJet pj(px,py,pz,e);
    double eta_r=pj.pseudorapidity();
    double phi_r=pj.phi();
    double pt_r=pj.pt();
    //cout << " e=" << e <<  " phi=" << pj.phi() << " eta=" << pj.eta() << endl;
    // fill hits
     LParticle p(px,py,pz,e,layer);
     p.SetCharge(layer);
     p.SetType(2); // ECAL 
     p.SetStatus(mcp->getNMCContributions());
     p.SetParameter( x*1000  );
     p.SetParameter( y*1000  );
     p.SetParameter( z*1000  );
     p.SetParameter( layer_pos_cm );
    // find fastest hit

    float timeCont = mcp->getTimeCont(0);
    EVENT::MCParticle* pmm =mcp->getParticleCont(0);
    int pdg=pmm->getPDG ();
    int status=pmm->getSimulatorStatus ();
    float rawTime = timeCont;
    float FAM = pmm->getMass();
    int nCont=mcp->getNMCContributions();
    
    for (int jjj=0; jjj<nCont; jjj++) {
                  if ( mcp->getTimeCont(jjj) < rawTime )
                       rawTime  = mcp->getTimeCont(jjj);
                       EVENT::MCParticle* pmm =mcp->getParticleCont(jjj);
                       pdg=pmm->getPDG ();
                       status=pmm->getSimulatorStatus();
                }
     p.SetParameter(rawTime); // fastest hit 
     p.SetParameter(avt);     // average hit time  
     p.SetParameter( (double)pdg  );
     p.SetParameter( (double)status  );
     p.SetParameter( (double)FAM );
//    avec_hits_raw_sf.push_back( pj );
  
// PDG of first constribution 

     if (mcp->getNMCContributions()>0){
         EVENT::MCParticle* pmm=mcp->getParticleCont(0);
         int pdg=pmm->getPDG ();
         int status=pmm->getSimulatorStatus ();
         p.SetParameter( pdg  );               
         p.SetParameter( (double)status  );
         //p.SetParameter( (double)(mcp->getGeneratorStatus()));
     }

    if(layer==1 or layer==31) simhits.push_back(p);
    // correct by SF (1st, 2nd, 3rd layer are 1., 0.0184, 0.0092)
    double ECAL_SF=0.0184;
    e=e/ECAL_SF;
    px =  e*x/_tmp;
    py =  e*y/_tmp;
    pz =  e*z/_tmp;

    }

    if(Truthjets_axis.size()>0)
      {
      int activeAreaRepeats_1 = 1;
      double ghostArea_1 = 0.01;
      double ghostEtaMax_1 = 7.0;
      fastjet::GhostedAreaSpec fjActiveArea_1(ghostEtaMax_1,activeAreaRepeats_1,ghostArea_1);
      fastjet::AreaDefinition fjAreaDefinition_1( fastjet::active_area, fjActiveArea_1 );
      fastjet::ClusterSequenceArea* thisClustering_reco = new fastjet::ClusterSequenceArea(avec_hits_raw_sf, jet_def, fjAreaDefinition_1);
      vector<fastjet::PseudoJet> sjets_reco = sorted_by_pt(thisClustering_reco->inclusive_jets(25.0));
      vector<TLorentzVector> Recojets;
          for (unsigned int k = 0; k<sjets_reco.size(); k++)
          {
              TLorentzVector p_using_reco;
              p_using_reco.SetPxPyPzE( sjets_reco[k].px(), sjets_reco[k].py(), sjets_reco[k].pz(),  sjets_reco[k].e());
              for(int iii=0 ; iii<Truthjets_axis.size() ; iii++)
              {
                  if(p_using_reco.DeltaR(Truthjets_axis[iii])<0.4) Recojets.push_back(p_using_reco);
                  
              }
              
          }
      
      vector<vector<TLorentzVector>> FourP_dR_Reco(Recojets.size(),vector<TLorentzVector>());
      vector<vector<int>>         PDG_Reco(Recojets.size(),vector<int>());
      vector<vector<double>>      PT_Reco_sort(Recojets.size(),vector<double>());
      vector<vector<double>>      PT_Reco(Recojets.size(),vector<double>());
      vector<vector<double>>      PT_sort_number_only(Recojets.size(),vector<double>());
      vector<vector<double>>      T_Reco_sort(Recojets.size(),vector<double>());
      vector<vector<double>>      T_Reco(Recojets.size(),vector<double>());
      vector<vector<double>>      T_sort_number_only(Recojets.size(),vector<double>());
      vector<vector<double>>      T_first_last_average(2,vector<double>());     

  
      vector<double>  mass_Reco={0,0,0,0,0,0,0,0,0,0};
      vector<int> event_number_Reco={0,0,0,0,0,0,0,0,0,0};
      vector<int> Eta_smaller_than_1_event={0,0,0,0,0,0,0,0,0,0};
      vector<int> event_number_Reco_for_mass={0,0,0,0,0,0,0,0,0,0};
      vector<int> Eta_smaller_than_1_event_for_mass={0,0,0,0,0,0,0,0,0,0};
      
    if(Recojets.size()>0)
          {
        cout << "88: ";
        for ( int Back_forth=0; Back_forth<Recojets.size(); Back_forth++) {
        for (int j1=0; j1<simhits.size(); j1++) {
 //       cout << "j1: " << j1 ;
        LParticle hit=(LParticle)simhits.at(j1);  
	TLorentzVector LE=hit.GetP();
          double e_h=LE.E();
          double phi_h=LE.Phi();
          double eta_h=LE.PseudoRapidity();
          vector<double> par=hit.GetParameters();
          int type= hit.GetType(); // ECAL or HCAL
          int layer=hit.GetCharge();
//	 cout << "layer: " << layer << endl;
          int x=int(par[0]);
          int y=int(par[1]);
          int z=int(par[2]);
          double layer_pos_cm=par[3];
          double Thit=par[4];
          double LogTime=TMath::Log10(Thit);
          double avt=par[5];
          int    pdg=int(par[6]);
          int    stat=int(par[7]);
          double Mass  = par[8];
	 
	  // Study of the dR
              //Hadronic decays checking
          	
		for(int k1=0 ; k1<Calhits.size(); k1++){
			LParticle Calhit=(LParticle)Calhits.at(k1);
			TLorentzVector LE_1=Calhit.GetP();
			vector<double> par1=Calhit.GetParameters();
			int CellX_Cal=int(par1[0]);
                        int CellY_Cal=int(par1[1]);
			int CellZ_Cal=int(par1[2]);
			int LAYER_ECAL_USE = int(par1[3]);
		//   cout << "Back_forth: " << Back_forth  << endl;
                if(layer==1  and (Recojets[Back_forth].DeltaR(LE_1))<0.4 and x==CellX_Cal and y==CellY_Cal and z==CellZ_Cal){
			T_first_last_average[0].push_back(Thit);
		}  
		if(layer==31 and (Recojets[Back_forth].DeltaR(LE_1))<0.4 and x==CellX_Cal and y==CellY_Cal and z==CellZ_Cal){
			T_first_last_average[1].push_back(Thit);
			//Mass
                      mass_Reco[Back_forth] = mass_Reco[Back_forth] + Mass;
			//Timing
       //               cout << "Timing: " <<Thit << endl;
                      T_Reco_sort[Back_forth].push_back(Thit);
                      T_Reco[Back_forth].push_back(Thit);
	            //Four_momentum
                      FourP_dR_Reco[Back_forth].push_back(LE);
		    //PT
                      PT_Reco_sort[Back_forth].push_back(LE.Perp());
		      PT_Reco[Back_forth].push_back(LE.Perp());
                      //PDG
			PDG_Reco[Back_forth].push_back(abs(pdg));
                      //Eta_selection
                      event_number_Reco[Back_forth] = event_number_Reco[Back_forth] + 1;
                      if(abs(eta_h)<1) Eta_smaller_than_1_event[Back_forth] = Eta_smaller_than_1_event[Back_forth] + 1;
		 }
		}}}
          // int    genstat=int(par[8]);
      //======================+Cut-up line===============//

        for (unsigned int Back_forth=0; Back_forth<Recojets.size(); Back_forth++) {
            sort(T_Reco_sort[Back_forth].begin() , T_Reco_sort[Back_forth].end());
            sort(PT_Reco_sort[Back_forth].begin(), PT_Reco_sort[Back_forth].end());}
            


	vector<vector<TLorentzVector>> Highest_PT_FourP(Recojets.size(),vector<TLorentzVector>());
                     
                     for(int Back_forth=0 ; Back_forth<Recojets.size() ; Back_forth++)
                     {
			 //
                         if(T_Reco_sort[Back_forth].size()>0){
                             PT_sort_number_only[Back_forth].push_back(PT_Reco_sort[Back_forth][0]);
                             T_sort_number_only[Back_forth].push_back(T_Reco_sort[Back_forth][0]);
                             for(int uuu=0; uuu<T_Reco_sort[Back_forth].size(); uuu++)
                             {
                                 if(PT_Reco_sort[Back_forth][uuu]!=PT_sort_number_only[Back_forth].back()) PT_sort_number_only[Back_forth].push_back(PT_Reco_sort[Back_forth][uuu]);
                                 if(T_Reco_sort[Back_forth][uuu] != T_sort_number_only[Back_forth].back()) T_sort_number_only[Back_forth].push_back(T_Reco_sort[Back_forth][uuu]);
                     }}}
  //      cout << "Check_point_fully_contained" << endl;
                    vector<int> Full_contain;
                    int check_point_eta;
                for(int Back_forth=0 ; Back_forth<Recojets.size() ; Back_forth++)
                    {
                     if(event_number_Reco[Back_forth]>0){
                         //cout << "Fraction_of_the_event_forth====> " << Eta_smaller_than_1_event[Back_forth]/event_number_Reco[Back_forth] << endl;
                         if((Eta_smaller_than_1_event[Back_forth]/event_number_Reco[Back_forth])>0.9)
                         {
                             Full_contain.push_back(1);
                         }
                         else{Full_contain.push_back(0); check_point_eta = check_point_eta +1;}
                     }
                        else{Full_contain.push_back(0);check_point_eta = check_point_eta +1;}
                     }
            
                     if(check_point_eta==Recojets.size()) continue;
            
                 
	         vector<float> dR_Highest_PT_T_Reco;
                 vector<float> dR_Highest_PT_PT_Reco;
                
		vector<vector<int>>         PT_PDG_Reco(Recojets.size(),vector<int>());
      		 vector<vector<int>>         T_PDG_Reco(Recojets.size(),vector<int>());
		
                double T_first=0 ; double T_last=0;

        if( T_first_last_average[0].size()!=0 and T_first_last_average[1].size()!=0  )
                {
                        float Time_Difference=0;
                        for(int G=0 ; G<T_first_last_average[0].size(); G++) T_first = T_first + T_first_last_average[0][G];
                        for(int H=0 ; H<T_first_last_average[1].size(); H++) T_last  = T_last  + T_first_last_average[1][H];
                        Time_Difference =  (T_last/T_first_last_average[1].size()) - (T_first/T_first_last_average[0].size());
                        cout << "Time_Difference: " << Time_Difference << endl;
                        if(Time_Difference>0) Timing_detecto_ECAL_TDif->Fill(Time_Difference);
                }

   //     cout << "Check_point_dR_calculation" << endl;
                     for(int Back_forth=0 ; Back_forth<Recojets.size() ; Back_forth++)
                     {
                         if(Full_contain[Back_forth]==1){
     //                        cout << "Back_forth_number====>: " << Back_forth << endl;
                             if(T_Reco_sort[Back_forth].size()>0)
                             {
                                 int Size_T_PT=T_Reco_sort[Back_forth].size();
                                 for(int jkl=0 ; jkl<Size_T_PT ; jkl++){
                                     if(PT_Reco_sort[Back_forth][Size_T_PT-1]==PT_Reco[Back_forth][jkl]) Highest_PT_FourP[Back_forth].push_back(FourP_dR_Reco[Back_forth][jkl]);
                                 }
				 
                                 for(int jkl=0 ; jkl<5 ; jkl++)
                                 {
                              //       cout << "jkl: " << jkl << endl;
                                     if(T_sort_number_only[Back_forth].size() >0 and PT_sort_number_only[Back_forth].size()>0)
                                     {
                                         //===================================================//
                                         if( jkl < T_sort_number_only[Back_forth].size() ){
                                             int identify_1=0;
                                             for(int ijk=0 ; ijk<Size_T_PT ; ijk++){
                                                 if(T_sort_number_only[Back_forth][T_sort_number_only[Back_forth].size()-1-jkl]==T_Reco[Back_forth][ijk])
                                                 {
						     if(ijk==0)Timing_detector_Reco_TOF->Fill(T_Reco[Back_forth][ijk]);
						     //cout << "T_Reco[Back_forth][ijk]: " << T_Reco[Back_forth][ijk] << endl;
						     //cout << "ijk: " << ijk << endl;
                                                     identify_1 = identify_1+1;
                                                     T_PDG_Reco[Back_forth].push_back(PDG_Reco[Back_forth][ijk]);
                                                     //cout << "T_PDG_Reco[Back_forth][ijk]: " << PDG_Reco[Back_forth][ijk] << endl;
                                                     dR_Highest_PT_T_Reco.push_back(FourP_dR_Reco[Back_forth][ijk].DeltaR(Highest_PT_FourP[Back_forth][0]));
                                                     h_Particles_dR_Highest_PT_T_Reco[jkl]->Fill(FourP_dR_Reco[Back_forth][ijk].DeltaR(Highest_PT_FourP[Back_forth][0]));
                                                     cout << "TTT:FourP_dR_Reco[Back_forth][ijk].DeltaR(Highest_PT_FourP[Back_forth][0]): " << FourP_dR_Reco[Back_forth][ijk].DeltaR(Highest_PT_FourP[Back_forth][0]) << endl;
                                                 }}
                                             if(identify_1>1) cout << "Weird! Check!"<< endl;}
                                         //===================================================/
                                         
					if( jkl < PT_sort_number_only[Back_forth].size() ){
                                             int identify=0;
                                             for(int ijk=0 ; ijk<Size_T_PT ; ijk++){
                                                 if(PT_sort_number_only[Back_forth][jkl]==PT_Reco[Back_forth][ijk])
                                                 {
						//cout << "PT_sort_number_only[Back_forth][jkl]: " << PT_sort_number_only[Back_forth][jkl] << "PT_Reco[Back_forth][ijk]: " << PT_Reco[Back_forth][ijk] << endl;
						     //cout << "ijk: " << ijk << endl;
                                                     identify = identify+1;
                                                     PT_PDG_Reco[Back_forth].push_back(PDG_Reco[Back_forth][ijk]);
                                                     //cout << "PT_PDG_Reco[Back_forth][ijk]: " << PDG_Reco[Back_forth][ijk] << endl;
                                                     dR_Highest_PT_PT_Reco.push_back(FourP_dR_Reco[Back_forth][ijk].DeltaR(Highest_PT_FourP[Back_forth][0]));
                                                     h_Particles_dR_Highest_PT_PT_Reco[jkl]->Fill(FourP_dR_Reco[Back_forth][ijk].DeltaR(Highest_PT_FourP[Back_forth][0]));
                                                     cout << "PTPTPT:FourP_dR_Reco[Back_forth][ijk].DeltaR(Highest_PT_FourP[Back_forth][0]): " << FourP_dR_Reco[Back_forth][ijk].DeltaR(Highest_PT_FourP[Back_forth][0]) << endl;
                                                 }}
                                             if(identify>1) cout << "Weird! Check_1!"<< endl;}
                                     }
                      }}}}

//for(int Back_forth=0 ; Back_forth<2 ; Back_forth++){
//	if(T_PDG_Reco[Back_forth].size()>0){
//	for(int jjjjj=0; jjjjj<T_PDG_Reco[Back_forth].size();jjjjj++) cout << "T_PDG_Reco[Back_forth]: " << T_PDG_Reco[Back_forth][jjjjj] << endl;}
//	if(PT_PDG_Reco[Back_forth].size()>0){
//        for(int jjjjj=0; jjjjj<PT_PDG_Reco[Back_forth].size();jjjjj++) cout << "PT_PDG_Reco[Back_forth]: " << PT_PDG_Reco[Back_forth][jjjjj] << endl;}
//}
//cout << "444: " << endl;
cout << "99: " ;
for(int Back_forth=0 ; Back_forth<Recojets.size() ; Back_forth++){
        for(int j=0 ; j<5 ; j++)
        {
	if(T_PDG_Reco[Back_forth].size()>0){
            if(  (T_PDG_Reco[Back_forth].size()) > j ){
		//cout << "abs(T_PDG_Reco[Back_forth][j]): " << abs(T_PDG_Reco[Back_forth][j]) << endl;
		int it;
                it=find(Trailing_particle_kind_T.begin(),Trailing_particle_kind_T.end(),abs(T_PDG_Reco[Back_forth][j]))[0];
                if(it!=abs(T_PDG_Reco[Back_forth][j]))
                {
                 //       cout << "============================================================================================================================================================" << endl;
		//	cout << "abs(T_PDG_Reco[Back_forth][j]): " << abs(T_PDG_Reco[Back_forth][j]) << endl;
                    Trailing_particle_kind_T.push_back(abs(T_PDG_Reco[Back_forth][j]));
                for(int m=0; m<Trailing_particle_kind_T.size();m++){
                    //cout << "Trailing_particle_kind_T[m]: "<< abs(Trailing_particle_kind_T[m]) << endl;
		    if(abs(T_PDG_Reco[Back_forth][j])==Trailing_particle_kind_T[m] and abs(T_PDG_Reco[Back_forth][j])!=22) 
			{h_Particles_Rank_T_Reco[j]->Fill(m);
                }
                    //cout << "Particle_ID_T_Reco[j]->GetBinContent(m): " << h_Particles_Rank_T_Reco[j]->GetBinContent(m+1) << endl;
		}}
 		//cout << "abs(T_PDG_Reco[Back_forth][j]): " << abs(T_PDG_Reco[Back_forth][j]) << endl;               
                else{
		for(int m=0; m<Trailing_particle_kind_T.size();m++){
                    //cout << "Trailing_particle_kind_T[m]: "<< abs(Trailing_particle_kind_T[m]) << endl;
                    if(abs(T_PDG_Reco[Back_forth][j])==Trailing_particle_kind_T[m] and abs(T_PDG_Reco[Back_forth][j])!=22) 
			{h_Particles_Rank_T_Reco[j]->Fill(m);
                }
                    //cout << "Particle_ID_T_Reco[j]->GetBinContent(m): " << h_Particles_Rank_T_Reco[j]->GetBinContent(m+1) << endl;
		}}
                }}
	  if(PT_PDG_Reco[Back_forth].size()>0){
             if( (PT_PDG_Reco[Back_forth].size()) > j ){
		//cout << "abs(PT_PDG_Reco[Back_forth][j]): " << abs(PT_PDG_Reco[Back_forth][j]) << endl;
		int it2;
                it2=find(Trailing_particle_kind_PT.begin(),Trailing_particle_kind_PT.end(),abs(PT_PDG_Reco[Back_forth][j]))[0];
                if(it2!=abs(PT_PDG_Reco[Back_forth][j]))
                {
		//	cout << "============================================================================================================================================================" << endl;
                  //      cout << "abs(PT_PDG_Reco[Back_forth][j]): " << abs(PT_PDG_Reco[Back_forth][j]) << endl;
                    Trailing_particle_kind_PT.push_back(abs(PT_PDG_Reco[Back_forth][j]));
                for(int m=0; m<Trailing_particle_kind_PT.size();m++){
                    //cout << "Trailing_particle_kind_PT[m]: "<< abs(Trailing_particle_kind_PT[m]) << endl;
                    if(abs(PT_PDG_Reco[Back_forth][j])==Trailing_particle_kind_PT[m] and abs(PT_PDG_Reco[Back_forth][j])!=22) 
			{h_Particles_Rank_PT_Reco[j]->Fill(m);
		}
                    //cout << "Particle_ID_PT_Reco[j]->GetBinContent(m): " << h_Particles_Rank_PT_Reco[j]->GetBinContent(m+1) << endl;
		}}
                //cout << "abs(PT_PDG_Reco[Back_forth][j]): " << abs(PT_PDG_Reco[Back_forth][j]) << endl;
                else{
		for(int m=0; m<Trailing_particle_kind_PT.size();m++){
                    //cout << "Trailing_particle_kind_PT[m]: "<< abs(Trailing_particle_kind_PT[m]) << endl;
                    if(abs(PT_PDG_Reco[Back_forth][j])==Trailing_particle_kind_PT[m] and abs(PT_PDG_Reco[Back_forth][j])!=22) 
			{h_Particles_Rank_PT_Reco[j]->Fill(m);
                }
                    //cout << "Particle_ID_PT_Reco[j]->GetBinContent(m): " << h_Particles_Rank_PT_Reco[j]->GetBinContent(m+1) << endl;
		}}}}
                
            }}
        //cout << "Check_point_trailing_dR_Tree" << endl;
                     //
		     cout << "99 : " ;
                     if(dR_Highest_PT_PT_Reco.size()>=1)
                     {
                         dR_Tr0PT_HPt_Reco = dR_Highest_PT_PT_Reco[0];
                     }
                     if(dR_Highest_PT_PT_Reco.size()>=2)
                     {
                         dR_Tr1PT_HPt_Reco = dR_Highest_PT_PT_Reco[1];
                     }
                     if(dR_Highest_PT_PT_Reco.size()>=3)
                     {
                         dR_Tr2PT_HPt_Reco = dR_Highest_PT_PT_Reco[2];
                     }
                     if(dR_Highest_PT_PT_Reco.size()>=4)
                     {
                         dR_Tr3PT_HPt_Reco = dR_Highest_PT_PT_Reco[3];
                     }
                     if(dR_Highest_PT_PT_Reco.size()>=5)
                     {
                         dR_Tr4PT_HPt_Reco = dR_Highest_PT_PT_Reco[4];
                     }
                     //
                     if(dR_Highest_PT_T_Reco.size()>=1)
                     {
                         dR_Tr0T_HPt_Reco = dR_Highest_PT_T_Reco[0];
                     }
                     if(dR_Highest_PT_T_Reco.size()>=2)
                     {
                         dR_Tr1T_HPt_Reco = dR_Highest_PT_T_Reco[1];
                     }
                     if(dR_Highest_PT_T_Reco.size()>=3)
                     {
                         dR_Tr2T_HPt_Reco = dR_Highest_PT_T_Reco[2];
                     }
                     if(dR_Highest_PT_T_Reco.size()>=4)
                     {
                         dR_Tr3T_HPt_Reco = dR_Highest_PT_T_Reco[3];
                     }
                     if(dR_Highest_PT_T_Reco.size()>=5)
                     {
                         dR_Tr4T_HPt_Reco = dR_Highest_PT_T_Reco[4];
                     }
        
        
cout << "2: " << endl;
     // } // close loop over  hits
            
            for(int Back_forth=0 ; Back_forth<Recojets.size() ; Back_forth++){
	             if(event_number_Reco[Back_forth]>0){
			// cout << "event_number_Reco[Back_forth]: " << event_number_Reco[Back_forth] << endl;
                        // cout << "Fraction_of_the_event_forth_for_mass====> " << Eta_smaller_than_1_event[Back_forth]/event_number_Reco[Back_forth] << endl;
                         if((Eta_smaller_than_1_event[Back_forth]/event_number_Reco[Back_forth])>0.9)
                         {
                             mass_sum_average_Reco->Fill(mass_Reco[Back_forth]/event_number_Reco[Back_forth]);
                             //cout << "mass_sum_average_Reco_forth_for_mass====> " << mass_Reco[Back_forth]/event_number_Reco[Back_forth] << endl;
                         }
                     }
                     }

      Full_contain.clear();}}
	====comment
	*/
      //Recojets.clear();
      //sjets_reco.clear();
      //thisClustering_reco.Clear();
      //  SimHIT.clear();

      /*
      avec_hits_raw_sf.clear();
      cout << "clear: " << endl;
      SimHIT.clear();
      Calhits.clear();
      sjets_truth.clear();
      Truthjets_axis.clear();
      truthjets.clear();
      Check_Forth_And_Back_Bool.clear();
      Forth_And_Back_Vector.clear();
      No_charge_PDG.clear();
      avec_truth.clear();     // created by generator
      avec_truth_sim.clear();*/
      // also created by geant
      //    cout << "1: " << endl;

      /*
   hist_ev++;

   // HCAL hits after created by slicPandora 
  double hcalsum=0;

  vector<PseudoJet> avec_hits;
  IMPL::LCCollectionVec* col51 = (IMPL::LCCollectionVec*) evt->getCollection("HAD_BARREL") ;
  nCL = col51->getNumberOfElements() ;
   for(int i=0 ; i<nCL ; ++i){
    // EVENT::SimCalorimeterHit* mcp =  (EVENT::SimCalorimeterHit*) col51->getElementAt(i) ;
    EVENT::CalorimeterHit* mcp =  (EVENT::CalorimeterHit*) col51->getElementAt(i) ;

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
    PseudoJet pj(px,py,pz,e);
    double eta_r=pj.pseudorapidity();
    double phi_r=pj.phi();
    double pt_r=pj.pt();
    //cout << " e=" << e <<  " phi=" << pj.phi() << " eta=" << pj.eta() << endl;
    avec_hits.push_back( pj );
  }


   //cout << "HCal raw sum=" << hcalsum_raw << endl;
   //cout << "HCal sum after SF=" << hcalsum << endl;



  double ecalsum=0;
  // ECAL hits
  IMPL::LCCollectionVec* col52 = (IMPL::LCCollectionVec*) evt->getCollection("EM_BARREL") ;
  nCL = col52->getNumberOfElements() ;
   for(int i=0 ; i<nCL ; ++i){
    // EVENT::SimCalorimeterHit* mcp =  (EVENT::SimCalorimeterHit*) col52->getElementAt(i) ;
    EVENT::CalorimeterHit* mcp =  (EVENT::CalorimeterHit*) col52->getElementAt(i) ;

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
    PseudoJet pj(px,py,pz,e);
    double eta_r=pj.pseudorapidity();
    double phi_r=pj.phi();
    double pt_r=pj.pt();
    //cout << " e=" << e <<  " phi=" << pj.phi() << " eta=" << pj.eta() << endl;
    avec_hits.push_back( pj );
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
              if ( pt < ETmin)                    continue;
              if ( fabs(eta)> ETAmax )            continue;
              LParticle p( sjets_clus[k].px(),sjets_clus[k].py(),sjets_clus[k].pz(),sjets_clus[k].e(),0);


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
              p.SetParameter(EffectiveRadius(sjets_clus[k],sjets_clus[k].constituents(),Rparam)); // 0 
              p.SetParameter(nsubjettiness(sjets_clus[k],sjets_clus[k].constituents(),1,Rparam)); // 1 
              p.SetParameter(nsubjettiness(sjets_clus[k],sjets_clus[k].constituents(),2,Rparam)); // 2 
              p.SetParameter(nsubjettiness(sjets_clus[k],sjets_clus[k].constituents(),3,Rparam)); //  3 
              p.SetParameter(splittingscale(sjets_clus[k])); // 4 
              p.SetParameter(eccentricity(sjets_clus[k],sjets_clus[k].constituents())); // 5
              p.SetParameter(hitsum); // 6 
              p.SetParameter(hitsum_raw); // 7 
              p.SetParameter(hitsum_raw_sf); // 8 

              // number of clusters in leading jet
              if (k==0) {
                        h_jet_n_clusters->Fill(sjets_clus[k].constituents().size());
                        vector<PseudoJet> constituents=sjets_clus[k].constituents(); 
                        unsigned int size=constituents.size();
                        h_jet_n_clusters->Fill(double(size));
                        for(unsigned int i =0 ; i < size; i++){
                            double et=constituents[i].Et();
                             h_jet_pt_clusters->Fill(et);
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
   h_jet_m_clus->Fill(mass);
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
   h_jetjet_m_clus->Fill( LL.M());
   
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
   for (int kk=0; kk<nmax; kk++){
   double x1=pow(2,kk+3);
   double x2=pow(2,kk+3+1);
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
*/

      // look at track resolution
      //
      // look at reconstructed tracks using Helix
      /*
=====comment  
double _bField=5;
// Reconstructed tracks
// look up at: /share/sl6/ilcsoft/slic/release-v05-00-00/slicPandora/HEAD/lcio/v02-04-03/build/include/EVENT
 vector<PseudoJet> avec_tracks;
 vector<LParticle> trackhits;

 IMPL::LCCollectionVec* colT = (IMPL::LCCollectionVec*) evt->getCollection( "Tracks"  ) ;
 unsigned int  nTracks = colT->getNumberOfElements() ;
 
for (unsigned int j=0; j<Forth_And_Back_Vector.size(); j++)
      {
          TLorentzVector Jet_axis_Truth=Forth_And_Back_Vector[j];

          for(unsigned int i=0 ; i<nTracks ; i++){
              EVENT::Track* track =  (EVENT::Track*) colT->getElementAt(i) ;
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
              PseudoJet pp(px,py,pz,e);
              double eta_r=pp.pseudorapidity();
              double phi_r=pp.phi();
              double pt_r=pp.pt();
              TLorentzVector TLV;
              TLV.SetPxPyPzE(px,py,pz,e);
             // Get the two 32-bit chunks of the ID.
             //===comment
             
              for(int ppp=0 ; ppp<track->getTrackerHits().size(); ppp++){
             int cellId0 = track->getTrackerHits()[ppp]->getCellID0();
             int cellId1 = track->getTrackerHits()[ppp]->getCellID1();
             cout << "cellId0: " << cellId0 << endl;
             cout << "cellId1: " << cellId1 << endl;
	     // Make a 64-bit id for the IDDecoder.  The type MUST be "long long" and not "long".  (from Tony Johnson)
             long long cellId = ((long long)cellId1) << 32 | cellId0;
             int layer = decoder->getFieldValue("layer", cellId);
             cout << "Tracker_Layer: "<< layer  << endl;
              continue;}
		=====comment//
             LParticle p(px,py,pz,e,0);
             
             if(TLV.DeltaR(Jet_axis_Truth)<0.4 and Check_Forth_And_Back_Bool[j]==1)
             {
                 trackhits.push_back(p);
             }
     // match reconstructed track with truth-level track
          } // end matching

     } // end track resolution
   // end single particle track resolution
	vector<int> Recojets_track={0,1};
if(Recojets_track.size()>0){
      vector<vector<TLorentzVector>> FourP_dR_Reco_track(Recojets_track.size(),vector<TLorentzVector>());
      vector<vector<int>>            PDG_Reco_track(Recojets_track.size(),vector<int>());
      vector<vector<double>>         PT_Reco_sort_track(Recojets_track.size(),vector<double>());
      vector<vector<double>>         PT_Reco_track(Recojets_track.size(),vector<double>());
      vector<vector<double>>         PT_sort_number_only_track(Recojets_track.size(),vector<double>());
      vector<vector<double>>         T_Reco_sort_track(Recojets_track.size(),vector<double>());
      vector<vector<double>>         T_Reco_track(Recojets_track.size(),vector<double>());
      vector<vector<double>>         T_sort_number_only_track(Recojets_track.size(),vector<double>());
      vector<double>  mass_Reco_track={0,0,0,0,0,0,0,0,0,0};
      vector<int> event_number_Reco_track={0,0,0,0,0,0,0,0,0,0};
      vector<int> Eta_smaller_than_1_event_track={0,0,0,0,0,0,0,0,0,0};
      vector<int> event_number_Reco_for_mass_track={0,0,0,0,0,0,0,0,0,0};
      vector<int> Eta_smaller_than_1_event_for_mass_track={0,0,0,0,0,0,0,0,0,0};
          for (unsigned int Back_forth=0; Back_forth<Recojets_track.size(); Back_forth++) {
              for (unsigned int j1=0; j1<trackhits.size(); j1++) {
                  //cout << "j1: " << j1 ;
                  LParticle hit=trackhits.at(j1);
                  TLorentzVector LE=hit.GetP();
                  double e_h=LE.E();
                  double phi_h=LE.Phi();
                  double eta_h=LE.PseudoRapidity();
                  vector<double> par=hit.GetParameters();
                  double Thit=0;
                  TLorentzVector Jet_axis_Truth=Forth_And_Back_Vector[Back_forth];

                  //mass_Reco[Back_forth] = mass_Reco[Back_forth] + Mass;
                  //Timing
                  //               cout << "Timing: " <<Thit << endl;
                  if( Jet_axis_Truth.DeltaR(LE)<0.4 ){
                  T_Reco_sort_track[Back_forth].push_back(Thit);
                  T_Reco_track[Back_forth].push_back(Thit);
                  //Four_momentum
                  FourP_dR_Reco_track[Back_forth].push_back(LE);
                  //PT
                  PT_Reco_sort_track[Back_forth].push_back(LE.Perp());
                  PT_Reco_track[Back_forth].push_back(LE.Perp());
                  //PDG
                  //PDG_Reco[Back_forth].push_back(abs(pdg));
                  //Eta_selection
                  event_number_Reco_track[Back_forth] = event_number_Reco_track[Back_forth] + 1;
                  if(abs(eta_h)<1) Eta_smaller_than_1_event_track[Back_forth] = Eta_smaller_than_1_event_track[Back_forth] + 1;
                  
              }}}
          // int    genstat=int(par[8]);
          //======================+Cut-up line===============//
          for (unsigned int Back_forth=0; Back_forth<Recojets_track.size(); Back_forth++) {
              sort(T_Reco_sort_track[Back_forth].begin() , T_Reco_sort_track[Back_forth].end());
              sort(PT_Reco_sort_track[Back_forth].begin(), PT_Reco_sort_track[Back_forth].end());}

          if(T_Reco_sort_track[0].size()>3){
              for(int i=0 ; i<T_Reco_sort_track[0].size() ; i++){
                 // cout << "T_Reco_sort_track[i]: "<< T_Reco_sort_track[0][i] << endl;
                 // cout << "PT_Reco_sort_track[i]: "<< PT_Reco_sort_track[0][i] << endl;
              }
          }
          vector<vector<TLorentzVector>> Highest_PT_FourP_track(Recojets_track.size(),vector<TLorentzVector>());
               cout << "5: " << endl;
          //		      cout << "New1 " << endl;
          for(int Back_forth=0 ; Back_forth<Recojets_track.size() ; Back_forth++)
          {
              //
              if(T_Reco_sort_track[Back_forth].size()>0){
                  PT_sort_number_only_track[Back_forth].push_back(PT_Reco_sort_track[Back_forth][0]);
                  T_sort_number_only_track[Back_forth].push_back(T_Reco_sort_track[Back_forth][0]);
                  for(int uuu=0; uuu<T_Reco_sort_track[Back_forth].size(); uuu++)
                  {
                      if(PT_Reco_sort_track[Back_forth][uuu]!=PT_sort_number_only_track[Back_forth].back()) PT_sort_number_only_track[Back_forth].push_back(PT_Reco_sort_track[Back_forth][uuu]);
                      if(T_Reco_sort_track[Back_forth][uuu] != T_sort_number_only_track[Back_forth].back()) T_sort_number_only_track[Back_forth].push_back(T_Reco_sort_track[Back_forth][uuu]);
                  }}}
          //      cout << "Check_point_fully_contained" << endl;
          vector<int> Full_contain_track;
          int check_point_eta_track;
          for(int Back_forth=0 ; Back_forth<Recojets_track.size() ; Back_forth++)
          {
              if(event_number_Reco_track[Back_forth]>0){
                  //cout << "Fraction_of_the_event_forth====> " << Eta_smaller_than_1_event[Back_forth]/event_number_Reco[Back_forth] << endl;
                  if((Eta_smaller_than_1_event_track[Back_forth]/event_number_Reco_track[Back_forth])>0.9)
                  {
                      Full_contain_track.push_back(1);
                  }
                  else{Full_contain_track.push_back(0); check_point_eta_track = check_point_eta_track +1;}
              }
              else{Full_contain_track.push_back(0);check_point_eta_track = check_point_eta_track +1;}
          }
          
          if(check_point_eta_track==Recojets_track.size()) continue;
          
               cout << "6: " << endl;
          vector<float>               dR_Highest_PT_T_Reco_track;
          vector<float>               dR_Highest_PT_PT_Reco_track;
          vector<vector<int>>         PT_PDG_Reco_track(Recojets_track.size(),vector<int>());
          vector<vector<int>>         T_PDG_Reco_track(Recojets_track.size(),vector<int>());
          
          //     cout << "Check_point_dR_calculation" << endl;
          for(int Back_forth=0 ; Back_forth<Recojets_track.size() ; Back_forth++)
          {
              if(Full_contain_track[Back_forth]==1){
                  //                        cout << "Back_forth_number====>: " << Back_forth << endl;
                  if(T_Reco_sort_track[Back_forth].size()>0)
                  {
                      int Size_T_PT=T_Reco_sort_track[Back_forth].size();
                      for(int jkl=0 ; jkl<Size_T_PT ; jkl++){
                          if(PT_Reco_sort_track[Back_forth][Size_T_PT-1]==PT_Reco_track[Back_forth][jkl]) Highest_PT_FourP_track[Back_forth].push_back(FourP_dR_Reco_track[Back_forth][jkl]);
                      }
                      
                      for(int jkl=0 ; jkl<5 ; jkl++)
                      {
                          cout << "jkl: " << jkl << endl;
                          if(T_sort_number_only_track[Back_forth].size() >0 and PT_sort_number_only_track[Back_forth].size()>0)
                          {
                              //===================================================//
                              if( jkl < T_sort_number_only_track[Back_forth].size() ){
                                  int identify_1=0;
                                  for(int ijk=0 ; ijk<Size_T_PT ; ijk++){
                                      if(T_sort_number_only_track[Back_forth][T_sort_number_only_track[Back_forth].size()-1-jkl]==T_Reco_track[Back_forth][ijk])
                                      {
        //                                  if(ijk==0)Timing_detector_Reco_TOF_track->Fill(T_Reco_track[Back_forth][ijk]);
                                          //cout << "T_Reco_track[Back_forth][ijk]: " << T_Reco_track[Back_forth][ijk] << endl;
                                          //cout << "ijk: " << ijk << endl;
                                          identify_1 = identify_1+1;
                                          dR_Highest_PT_T_Reco_track.push_back(FourP_dR_Reco_track[Back_forth][ijk].DeltaR(Highest_PT_FourP_track[Back_forth][0]));
                                          h_Particles_dR_Highest_PT_T_Reco_track[jkl]->Fill(FourP_dR_Reco_track[Back_forth][ijk].DeltaR(Highest_PT_FourP_track[Back_forth][0]));
                                   //       cout << "TTT:FourP_dR_Reco_track[Back_forth][ijk].DeltaR(Highest_PT_FourP_track[Back_forth][0]): " << FourP_dR_Reco_track[Back_forth][ijk].DeltaR(Highest_PT_FourP_track[Back_forth][0]) << endl;
                                      }}
			          //cout << "identify_1: " << identify_1 << endl;
                                  //if(identify_1>1) cout << "Weird! Check!_track"<< endl;
                                  }
                              //===================================================/
                              
                              if( jkl < PT_sort_number_only_track[Back_forth].size() ){
                                  int identify=0;
                                  for(int ijk=0 ; ijk<Size_T_PT ; ijk++){
                                      if(PT_sort_number_only_track[Back_forth][jkl]==PT_Reco_track[Back_forth][ijk])
                                      {
                                          //cout << "ijk: " << ijk << endl;
                                          identify = identify+1;
                                          dR_Highest_PT_PT_Reco_track.push_back(FourP_dR_Reco_track[Back_forth][ijk].DeltaR(Highest_PT_FourP_track[Back_forth][0]));
                                          h_Particles_dR_Highest_PT_PT_Reco_track[jkl]->Fill(FourP_dR_Reco_track[Back_forth][ijk].DeltaR(Highest_PT_FourP_track[Back_forth][0]));
                                          cout << "PTPTPT:FourP_dR_Reco_track[Back_forth][ijk].DeltaR(Highest_PT_FourP_track[Back_forth][0]): " << FourP_dR_Reco_track[Back_forth][ijk].DeltaR(Highest_PT_FourP_track[Back_forth][0]) << endl;
                                      }}
                                  if(identify>1) cout << "Weird! Check_1!_track"<< endl;
                                  }
                          }
                      }}}}
         
          //cout << "Check_point_trailing_dR_Tree" << endl;
          //
          if(dR_Highest_PT_PT_Reco_track.size()>=1)
          {
              dR_Tr0PT_HPt_Reco_track = dR_Highest_PT_PT_Reco_track[0];
          }
          if(dR_Highest_PT_PT_Reco_track.size()>=2)
          {
              dR_Tr1PT_HPt_Reco_track = dR_Highest_PT_PT_Reco_track[1];
          }
          if(dR_Highest_PT_PT_Reco_track.size()>=3)
          {
              dR_Tr2PT_HPt_Reco_track = dR_Highest_PT_PT_Reco_track[2];
          }
          if(dR_Highest_PT_PT_Reco_track.size()>=4)
          {
              dR_Tr3PT_HPt_Reco_track = dR_Highest_PT_PT_Reco_track[3];
          }
          if(dR_Highest_PT_PT_Reco_track.size()>=5)
          {
              dR_Tr4PT_HPt_Reco_track = dR_Highest_PT_PT_Reco_track[4];
          }
          //
          if(dR_Highest_PT_T_Reco_track.size()>=1)
          {
              dR_Tr0T_HPt_Reco_track = dR_Highest_PT_T_Reco_track[0];
          }
          if(dR_Highest_PT_T_Reco_track.size()>=2)
          {
              dR_Tr1T_HPt_Reco_track = dR_Highest_PT_T_Reco_track[1];
          }
          if(dR_Highest_PT_T_Reco_track.size()>=3)
          {
              dR_Tr2T_HPt_Reco_track = dR_Highest_PT_T_Reco_track[2];
          }
          if(dR_Highest_PT_T_Reco_track.size()>=4)
          {
              dR_Tr3T_HPt_Reco_track = dR_Highest_PT_T_Reco_track[3];
          }
          if(dR_Highest_PT_T_Reco_track.size()>=5)
          {
              dR_Tr4T_HPt_Reco_track = dR_Highest_PT_T_Reco_track[4];
          }
          
          
          
        // close loop over  hits
          for(int Back_forth=0 ; Back_forth<Recojets_track.size() ; Back_forth++){
	             if(event_number_Reco_track[Back_forth]>0){
                     // cout << "event_number_Reco[Back_forth]: " << event_number_Reco[Back_forth] << endl;
                     // cout << "Fraction_of_the_event_forth_for_mass====> " << Eta_smaller_than_1_event[Back_forth]/event_number_Reco[Back_forth] << endl;
                     if((Eta_smaller_than_1_event_track[Back_forth]/event_number_Reco_track[Back_forth])>0.9)
                     {
                         mass_sum_average_Reco_track->Fill(mass_Reco_track[Back_forth]/event_number_Reco_track[Back_forth]);
                         cout << "mass_sum_average_track_Reco_forth_for_mass====> " << mass_Reco_track[Back_forth]/event_number_Reco_track[Back_forth] << endl;
                     }
                 }
              if(event_number_Reco_track[Back_forth]>0){
                  //cout << "event_number_Reco[Back_forth]: " << event_number_Reco[Back_forth] << endl;
                  //cout << "Fraction_of_the_event_back_for_mass====> " <<  Eta_smaller_than_1_event[Back_forth]/event_number_Reco[Back_forth] << endl;
                  if((Eta_smaller_than_1_event_track[Back_forth]/event_number_Reco_track[Back_forth])>0.9)
                  {
                      mass_sum_average_Reco_track->Fill(mass_Reco_track[Back_forth]/event_number_Reco_track[Back_forth]);
                      cout << "mass_sum_average_Reco_track_back_for_mass====> " << mass_Reco_track[Back_forth]/event_number_Reco_track[Back_forth] << endl;
                  }
              }}
      }*/
      T->Fill();
      T_Reco_T->Fill();
      T_Reco_T_track->Fill();
      cout << "Final: ";
      // end loop
    }

    lcReader->close();
    delete lcReader;

  } // close the file

  //m_ntuple->Fill();
  RootFile->Write();
  //RootFile->Print();
  RootFile->Close();

  cout << "Total hit energy in HCAL for antiKT5=" << XEnergy << endl;
  cout << "Total time*energy in HCAL for antiKT5 =" << XTime << endl;
  cout << "Weighted Total time in HCAL [ns] =" << XTime / XEnergy << endl;

  cout << "Writing ROOT file " + outputfile << endl;

  return 0;
}

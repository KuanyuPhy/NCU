#include <iostream>
#include <fstream>
#include <stdlib.h>

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
#include "TNtuple.h"
#include "TTree.h"

using namespace std;

const double kPI = TMath::Pi();
const double k2PI = 2 * kPI;
#include "fastjet/PseudoJet.hh"
#include "fastjet/ClusterSequence.hh"
#include "fastjet/GhostedAreaSpec.hh"
#include <fastjet/AreaDefinition.hh>
#include <fastjet/ClusterSequenceArea.hh>
using namespace fastjet;

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

int main(int argc, char **argv)
{
  std::vector<std::string> files = open("data.in");
  int mtype = 1;

  //for (auto i = files.begin(); i != files.end(); ++i)
  //  cout << "files = " << i << endl;

  string outputfile = "root/output.root";
  //cout << "\n -> Output file is =" << outputfile << endl;
  int gg;
  TTree *mytree = new TTree("mytree", "this is a plain tree");
  mytree->Branch("gg", &gg, "gg/I");
  TH1F *Event_number_check = new TH1F("Event_number_check", "Event_number_check", 12, 0, 12);
  TFile *RootFile = new TFile(outputfile.c_str(), "UPDATE", "Histogram file");
  TH1D *h_debug = new TH1D("debug", "events", 10, 0, 10);

  double TTxbins[] = {0.0, 0.1, 0.15, 0.2, 0.25, 0.3, 0.35, 0.4, 0.45, 0.5, 0.55, 0.6, 0.65, 0.7, 0.75, 0.8, 0.85, 0.9, 0.95, 1., 1.1, 1.2, 1.4, 1.6, 1.8, 2.0, 2.5, 3.0, 4.0, 6.0, 8.0, 10.0, 20.0, 30};
  const int TTBins = sizeof(TTxbins) / sizeof(double);

  TH1D *firstLayerTime = new TH1D("firstLayerTime", "First Layer Time", 100, 7.0, 8.0);
  firstLayerTime->GetXaxis()->SetTitle("T[ns]");
  firstLayerTime->GetYaxis()->SetTitle("Entries");

  TH1D *lastLayerTime = new TH1D("lastLayerTime", "last Layer Time", 100, 7.0, 8.0);
  lastLayerTime->GetXaxis()->SetTitle("T[ns]");
  lastLayerTime->GetYaxis()->SetTitle("Entries");

  TH1D *h_jet_pt_truth_mass = new TH1D("Mass", "Jet mass", 100, 0, 10000);

  TH1D *OwnLayerTime = new TH1D("OwnLayerTime", "Time difference between 31 nd 0 layers for 1 GeV", 1000, 0.0, 1.0);

  TH1D *TimeEcalDiff1 = new TH1D("time_ecal_diff1gev", "Time difference between 31 nd 0 layers for 1 GeV", TTBins - 1, TTxbins);
  TH1D *TimeEcalDiff10 = new TH1D("time_ecal_diff10gev", "Time difference between 31 nd 0 layers for 10 GeV", TTBins - 1, TTxbins);
  TProfile *TimeEcalDiffPt = new TProfile("time_ecal_diff vs pt", "Time difference between 31 nd 0 layers vs pT", 20, 0, 20, 's');

  TH1D *binsTT = new TH1D("bins_time_ecal", "bins_time_ecal", TTBins - 1, TTxbins);
  binsTT->Sumw2();
  for (Int_t j = 0; j < TTBins - 1; j++)
  {
    float x = TTxbins[j + 1] - TTxbins[j];
    binsTT->Fill(TTxbins[j] + 0.5 * x, x);
  }
  TH1D *h_jet_pt_truth_sim = new TH1D("jet_pt_truth_sim", "pT [GeV] plus Geant4", 100, 0, 3000);
  TH1D *h_eta_jet = new TH1D("jet_eta", "eta jets", 100, -4, 4);
  TH1D *pz_gamma = new TH1D("pz_gamma", "#gamma pz [GeV]", 10, 0, 3000);
  pz_gamma->GetXaxis()->SetTitle("[GeV]");
  pz_gamma->GetYaxis()->SetTitle("Entries");

  TH1D *checkgs = new TH1D("checkgs", "checkgs", 40, 0, 4);

  Int_t Event;
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

  //calculate the Event pass cut
  Long64_t nPass[20] = {0};

  // calculate position
  double layer_size_mm = 27.5 + 5 + 2.5;
  double hcal_inner_R_mm = 2300;

  double layer_size_ecal_mm = 4.0;
  double ecal_inner_R_mm = 2100;

  // calculate weighted average of time
  double XTime = 0;
  double XEnergy = 0;

  const pandora::SubDetectorType subDetectorType = geom->getPandoraSubDetectorType(caloType);

  // *tupleNames = "px:py:pz:vx:vy:vz:ex:ey:ez:pdg:np:nd:gs:ss";
  //TNtupleD *tuple = new TNtupleD("MCParticle", "", tupleNames);
  TNtuple *tuple = new TNtuple("tuple", "a n-tuple", "px:py:pz:vx:vy:vz:ex:ey:ez:pdg:np:nd:gs:ss");

  int var[13];

  double minPtConst = 0.2; // min pT on constituents
  // jets
  double Rparam = 0.4;
  const double ETAmax = 0.6;
  double ETmin = 0.5;
  if (mtype == 1)
    ETmin = 200; // increase for boosted

  if (mtype == 1)
    cout << "mu+mu- mode for boosted jets" << endl;

  cout << "min PT for jets=" << ETmin << endl;
  cout << "eta max for jets=" << ETAmax << endl;
  cout << "R for jets =" << Rparam << endl;

  // fastjet
  Strategy strategy = fastjet::Best;
  JetDefinition jet_def(fastjet::antikt_algorithm, Rparam, strategy);

  int MaxEvents = 100000000;

  int nEvents = 0;
  int nnEvents = 0;

  int Hadronic_decay_total = 0;
  int Leptonic_decay_total = 0;

  // loop over all files
  for (unsigned int mfile = 0; mfile < files.size(); mfile++)
  {
    string Rfile = files[mfile];

    cout << " # File=" << Rfile << endl;

    IO::LCReader *lcReader = IOIMPL::LCFactory::getInstance()->createLCReader();
    lcReader->open(Rfile.c_str());
    cout << "File_name" << Rfile.c_str() << endl;

    EVENT::LCEvent *evt = 0;

    if (nEvents > MaxEvents)
      break;
    //----------- the event loop -----------
    nnEvents = 0;
    while ((evt = lcReader->readNextEvent()) != 0)
    {

      if (nEvents == 0)
        UTIL::LCTOOLS::dumpEvent(evt);

      // UTIL::LCTOOLS::dumpEvent( evt ) ;
      nnEvents++;
      nEvents++;
      //if ((nEvents < 100 && nEvents % 10 == 0) || (nEvents > 100 && nEvents % 200 == 0))
      //cout << "nEvents: " << nEvents << endl;
      //cout << " # Events=" << nEvents << endl;
      Event_number_check->Fill(1);

      if (nEvents > MaxEvents)
        break;

      h_debug->Fill(1.0);

      std::string mcpName("MCParticle");
      // get truth
      IMPL::LCCollectionVec *col = (IMPL::LCCollectionVec *)evt->getCollection(mcpName);
      int nMCP = col->getNumberOfElements();

      int neu = 0;
      //list of Particle
      vector<int> PDG_with_no_charge = {0};
      vector<PseudoJet> avec_truth;     // created by generator
      vector<PseudoJet> avec_truth_sim; // also created by geant
                                        //==============================================================//
      int Forth = 1;
      int Back = -1;
      vector<int> Check_Forth_And_Back = {Forth, Back};
      vector<bool> Check_Forth_And_Back_Bool;
      vector<TLorentzVector> Forth_And_Back_Vector;
      int Zprime_pdg = 32;
      int Photon_pdg = 22;
      int Muon_pdg = 13;
      int W_pdg = 24;
      //cout << "nMCP = " << nMCP << endl;
      //Check the leptonic decay and hadronic decay
      for (int CFAB = 0; CFAB < 2; CFAB++)
      {
        int Leptonic_check = 0;

        for (int i = 0; i < nMCP; ++i)
        {
          EVENT::MCParticle *mcp = (EVENT::MCParticle *)col->getElementAt(i);
          if (mcp->getParents().size() != 0)
          {
            if ((mcp->getParents()[0]->getPDG() == 32) and (mcp->getPDG()) * Check_Forth_And_Back[CFAB] > 0)
            {
              int gg = mcp->getGeneratorStatus();
              checkgs->Fill(gg);
              if (mcp->getGeneratorStatus() == 3)
              {
                TLorentzVector p;
                p.SetPxPyPzE(mcp->getMomentum()[0], mcp->getMomentum()[1], mcp->getMomentum()[2], mcp->getMomentum()[3]);
                Forth_And_Back_Vector.push_back(p);
                for (unsigned int j = 0; j < (mcp->getDaughters().size()); j++)
                {
                  if ((abs(mcp->getDaughters()[j]->getPDG()) < 19) and (abs(mcp->getDaughters()[j]->getPDG()) > 10))
                  {
                    Leptonic_check = Leptonic_check + 1;
                  }
                }
              }
            }
            if (Leptonic_check != 0)
            {
              Leptonic_decay_total = Leptonic_decay_total + 1;
              //cout << "Awful leptonic decay:" << endl;
              Check_Forth_And_Back_Bool.push_back(false);
            }
            else
            {
              Hadronic_decay_total = Hadronic_decay_total + 1;
              //cout << "Good Jet! Hadronic decay:" << endl;
              Check_Forth_And_Back_Bool.push_back(true);
            }
          }
        }
        //cout << "Check_Forth_And_Back_Bool size = " << Check_Forth_And_Back_Bool.size() << endl;
        //cout << "nMCP =" << nMCP << endl;
        mytree->Fill();
      }
      cout << "Check_Forth_And_Back_Bool size = " << Check_Forth_And_Back_Bool.size() << endl;
      /*
      for (int i = 0; i < 10; i++)
      {
        cout << "i = " << i << "Check_Forth_And_Back_Bool  = " << Check_Forth_And_Back_Bool[i] << endl;
      }*/

      for (int i = 0; i < nMCP; ++i)
      {

        EVENT::MCParticle *mcp = (EVENT::MCParticle *)col->getElementAt(i);
        double px = mcp->getMomentum()[0];
        double py = mcp->getMomentum()[1];
        double pz = mcp->getMomentum()[2];
        double m = mcp->getMomentum()[3];
        double e = sqrt(px * px + py * py + pz * pz + m * m);
        int pdgid = mcp->getPDG();
        //cout << "m=" << m << " |p|=" << sqrt(px*px+py*py+pz*pz) << " e=" << e << endl;
        if (mcp->getCharge() == 0)
        {

          int itt;
          itt = find(PDG_with_no_charge.begin(), PDG_with_no_charge.end(), abs(pdgid))[0]; //retuen [0] element
          if (itt != abs(pdgid))
          {
            //cout << "abs(pdgid) =" << abs(pdgid) << endl;
            PDG_with_no_charge.push_back(abs(pdgid));
          }
        }

        fastjet::PseudoJet p(px, py, pz, e);
        //p.SetPxPyPzE(px, py, pz, e);
        p.set_user_index(pdgid);
        //cout << "test1" << endl;
        // only generator level

        int pdg = mcp->getPDG();
        int np = mcp->getParents().size();
        int nd = mcp->getDaughters().size();
        int gs = mcp->getGeneratorStatus();
        if (abs(pdg) == 22 and gs == 1 and abs(mcp->getParents()[0]->getPDG()) == 13)
        {
          pz = abs(mcp->getParents()[0]->getMomentum()[2]) > 2000;
          pz_gamma->Fill(pz);
        }

        if (abs(pdg) == 22 and gs == 1 and abs(mcp->getParents()[0]->getPDG()) == 13 and abs(mcp->getParents()[0]->getMomentum()[2]) > 2000)
        {
          continue;
        }
        if (gs == 1)
        {
          avec_truth.push_back(p);
        }
      }
      // assume remnant for mu+mu-
      //cout << "test6" << endl;
      int activeAreaRepeats = 1;
      double ghostArea = 0.01;
      double ghostEtaMax = 7.0;
      fastjet::GhostedAreaSpec fjActiveArea(ghostEtaMax, activeAreaRepeats, ghostArea);
      //cout << "test7" << endl;
      fastjet::AreaDefinition fjAreaDefinition(fastjet::active_area, fjActiveArea);
      //cout << "test8" << endl;
      fastjet::ClusterSequenceArea *thisClustering = new fastjet::ClusterSequenceArea(avec_truth, jet_def, fjAreaDefinition);
      //cout << "test9" << endl;
      vector<fastjet::PseudoJet> sjets_truth = sorted_by_pt(thisClustering->inclusive_jets(25.0));
      vector<LParticle> truthjets;
      int nn = 0;
      int check = 4;
      int Jet_each_event = 0;
      vector<TLorentzVector> Truthjets_axis;
      //cout << sjets_truth.size() << endl;
      for (unsigned int k = 0; k < sjets_truth.size(); k++)
      {
        //cout << "test8" << endl;
        double pt = sjets_truth[k].perp();
        double eta = sjets_truth[k].pseudorapidity();
        if (fabs(eta) > ETAmax)
          continue;
        if (pt < 1.5)
          continue;
        h_jet_pt_truth_sim->Fill(pt);
        //h_jet_pt_truth_mass->Fill(mass);
        h_eta_jet->Fill(eta);
        //cout << "pt" << endl;
      }

      //cout << "Final: " << endl;

    } //end loop
    cout << "nnEvents = " << nnEvents << endl;
    lcReader->close();
    delete lcReader;
  }

  RootFile->Write();
  mytree->Write();
  Event_number_check->Write();
  //RootFile->Print();
  RootFile->Close();
  cout << "end" << endl;

  return 0;
}
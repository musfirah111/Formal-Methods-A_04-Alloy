
one sig NationalHolidays {
  dates: set String
}
abstract sig CaseStatus {}
one sig Open, Closed extends CaseStatus {}

abstract sig Person {
  id: one String,
  name: one String,
  email: one String,
  phoneNumber: one Int,
  dob: one String,
  gender: one String
}

sig Patient extends Person {
  prescription: some Prescription,
  appointment: some Appointment,
  bill: some Bill,
  ehr: one EHR,
  dischargeSummary: lone DischargeSummary,
  bed: lone Bed,
  caseStatus: one CaseStatus
}

sig Staff extends Person {
  type: one String,
  isOnLeave: one Int,
  qualification: some String,
  assignedShifts: set Shift
}

sig Doctor extends Staff {
  maxAppointmentsPerDay: one Int,
  rank: one String,
  appointments: set Appointment
}

sig Appointment {
  id: one String,
  type: one String,
  date: one String,
  status: one String,
  doctor: one Doctor,
  patient: one Patient,
  resources: some Resource,
  labTests: some LabTest,
  remainder: lone Remainder,
  timeSlot: one TimeSlot
}

sig Prescription {
  id: one String,
  medicines: some Medicine,
  appointment: one Appointment
}

sig Bill {
  totalAmount: one Int,
  isPaid: one Int,
  appointment: one Appointment
}

sig LabTest {
  id: one Int,
  appointment: one Appointment,
  testCost: one Int
}

sig EHR {
  id: one Int,
  dateCreated: one String,
  currentMedications: set Medicine,
  pastSurgeries: set Surgery,
  labTests: set LabTest,
  allergies: set Allergy,
  patient: one Patient,
  receivedtreatment: one Int
}

sig Bed {
  id: one Int,
  location: one String,
  isOccupied: one Int,
  assignedPatient: lone Patient,
  type: one String //"General Ward", "ICU", "CCU"
}

sig Surgery {
  id: one Int,
  anesthetist: one Staff,
  assignedOT: one String,
  appointment: one Appointment
}

sig DischargeSummary {
  summaryID: one Int,
  dischargeDate: one String,
  status: one String,
  signedBy: one Doctor,
  patient: one Patient
}

sig Pharmacy {
  medicines: some Medicine
}

sig Medicine {
  id: one String,
  name: one String,
  stock: one Int,
  threshold: one Int,
  allergens: set String,
  medicineCost: one Int
}

sig Allergy {
  allergyID: one String,
  name: one String,
  severity: one String,
  reaction: lone String,
  isClinicallyConfirmed: one Int,
  identificationDate: lone String
}

sig Resource {
  type: one String,
  isAvailable: one Int,
  resourceCost: one Int,
  appointment: one Appointment
}

sig Shift {
  id: one Int,
  date: one String,
  type: one String,  //Doctor, Nurse, QualityAssuranceTeam
  location: one String, 
  startingTime: one Time,
  endingTime: one Time,
  timeSlot: set TimeSlot,
  assignedTo: set Staff
}

sig TimeSlot {
  startingTime: one Time,
  endingTime: one Time
}

// Time.
sig Time {
  hour: one Int,
  minute: one Int
}

sig OperationTheater {
  id: one Int
}

sig Remainder {
  id: one Int,
  sentTime: one Time,
  remainderOfAppointment: one Appointment
}


sig Feedback {
  id: one Int,
  rating: one Int,
  comment: lone String,
  appointment: one Appointment,
  notifiedTeam: set Staff // Relation to staff of type "QualityAssuranceTeam"
}

sig LowStockAlert {
  medicine: one Medicine,
  generatedOn: one String,
  sentTo: one Staff
}


fun timeInMinutes[t: Time]: Int {
  mul[t.hour, 60] + t.minute
}


//<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<Simple Structural>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

//A doctor can be assigned to multiple patients.
fact DoctorCanHaveMultiplePatients {
  all d: Doctor |
    #({ p: Patient | some a: d.appointments | a.patient = p }) > 1
}

assert DoctorCanHaveMultiplePatientsAssertion {
  all d: Doctor |
    #({ p: Patient | some a: d.appointments | a.patient = p }) > 1
}

check DoctorCanHaveMultiplePatientsAssertion for 5


//A resource can be assigned to only one patient at a time.
fact ResourceAssignedToOnePatient {
  all r1, r2: Resource |
    r1 != r2 and r1.appointment.patient != r2.appointment.patient => r1 != r2
}

//Each appointment is linked to one doctor and one patient.
fact EachAppointmentLinkedToDoctorAndPatient {
  all a: Appointment |
    one a.doctor and one a.patient
}

//Each prescription is issued by a registered doctor.
fact PrescriptionsAreIssuedByDoctors {
  all p: Prescription |
    one p.appointment.doctor
}

//Every bill corresponds to a single patient.
fact BillLinkedToOnePatient {
  all b: Bill | one b.appointment.patient
}

//<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<Business or Real World Rules (5 - 10)>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

//Appointments cannot be scheduled on national holidays except in emergencies.
fact NoAppointmentOnNationalHolidaysExceptEmergency{
   all a: Appointment | a.date in NationalHolidays.dates implies a.type = "Emergency"
}

//ICU patients must have 24/7 nursing.
fact ICUPatientsHaveNursing24_7{
  all p: Patient |
    p.bed != none and p.bed.type = "ICU" implies
      some s1, s2, s3: Shift, n1, n2, n3: Staff |
        n1.type = "Nurse" and n1 in s1.assignedTo and
        n2.type = "Nurse" and n2 in s2.assignedTo and
        n3.type = "Nurse" and n3 in s3.assignedTo
}

//A discharge summary must be reviewed and signed by a senior doctor.
fact DischargeSummaryReviewdAndSignedBySeniorDoctor {
  all ds: DischargeSummary |
    ds.signedBy.rank = "Senior"
}

//Emergency appointments override schedules.
fact EmergencyAppointmentsOverRideScdedules {
  all a1, a2: Appointment |
    a1 != a2 and 
    a1.date = a2.date and 
    a1.timeSlot = a2.timeSlot and 
    a1.doctor = a2.doctor and
    a1.type != "Emergency" and
    a2.type != "Emergency" =>
      a1.status = "Cancelled" or a2.status = "Cancelled"
}

//Poor feedback triggers a review.
fact PoorFeedbackTriggersReview {
   all f: Feedback |
    f.rating < 3 => {
      some qa: Staff | qa.type = "QualityAssuranceTeam" and qa in f.notifiedTeam
    }
}


//<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<Moderate Logic Rules>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>

// Appointments are only allowed if a doctor is available.
fact AppointmentAllowedOnlyIfDoctorAvailable {
  all a: Appointment |
    some s: a.doctor.assignedShifts | s.date = a.date
}

// If a patient cancels an appointment, the time slot should become available again.
fact CancelledAppointmentFreesTimeSlot {
  all ts: TimeSlot |
    some a: Appointment | a.status = "cancelled" and a.timeSlot = ts =>
      all a2: Appointment | a2.timeSlot = ts implies a2.status = "cancelled"
}

//  If the medicine stock is less than the minimum threshold, notify the pharmacy admin.
fact GenerateAlertWhenStockLow {
  all m: Medicine |
    m.stock < m.threshold =>
      some a: LowStockAlert |
        a.medicine = m and
        some s: Staff |
          s.type = "PharmacyAdmin" and
          a.sentTo = s
}

// If a staff member is marked on leave, they cannot be assigned to duties that day.
fact StaffOnLeaveNotAssignedToShifts {
  all s: Staff |
    s.isOnLeave = 1 =>
      all sh: Shift |
        sh in s.assignedShifts implies no sh
}

// If the doctor has more than 25 patients in a day, no further appointments can be scheduled.
fact PerDayMax25PatientsPerDoctor {
  all d: Doctor, day: String |
    #({ a: Appointment | a.doctor = d and a.date = day }.patient) <= 25
}

// Feedback can only be submitted after the appointment status is “Completed.”
fact FeedbackOnlyAfterCompletedAppointment {
  all f: Feedback |
    f.appointment.status = "Completed"
}

// Appointment reminders must be sent 24 hours before the scheduled time.
fact remainderForAppointment {
  all a: Appointment | 
    some a.remainder => {
      let r = a.remainder,
          apptTime = a.timeSlot.startingTime,
          sentTime = r.sentTime |
        apptTime.hour - sentTime.hour = 24 and
        apptTime.minute = sentTime.minute
    }
}

// If a patient receives any treatment, then a billing entry must be automatically generated for the services used.
fact automaticBillGeneration {
  all p: Patient |
    all a: p.appointment |
      one e: EHR | e.patient = p and e.receivedtreatment = 1 implies
        some b: Bill | b.appointment = a
}

// Discharge summary must be uploaded before closing a patient case file.
fact DischargeSummaryBeforeCaseClosure {
  all p: Patient |
    p.caseStatus = Closed implies p.dischargeSummary != none and p.dischargeSummary.patient = p
}

// If a patient is assigned to the ICU, the system must auto-assign a nurse.
fact AutoAssignedNurseToICUPatient {
  all p: Patient |
    p.bed.isOccupied = 1 and p.bed.location = "ICU" implies
      some n: Staff |
        n.type = "Nurse" and
        some s: n.assignedShifts |
          s.date = p.appointment.date and
          s.location = "ICU"
}

// Assertion to Verify

// All patients must have at least one EHR entry.
fact AtleastOneEHREntry {
  all p: Patient |
    some ehr: EHR | ehr.patient = p
}


// All bills must match the sum of resources, lab tests, and medication costs.
fact BillMatchTheSum {
  // all b: Bill | 
  //   b.totalAmount = let totalSum |
  //   totalSum = r: Resource |
  //   r.resourceCost + l: LabTest |
  //   l.testCost + m: Medicine |
  //   m.medicineCosts
}

// Meds can’t be issued without a prescription.
fact MedsCannotBeIssuedWithoutPrescription {
  all m: Medicine |
    some p: Prescription | p.medicines = m => some p
}

// Feedback must be linked to completed appointments.
fact FeedbackLinkedToCompletedAppointments {
  all f: Feedback |
    f.appointment.status = "Completed" and f.appointment = f.appointment
}

// A resource must be available before it can be booked.
fact ResourceAvailabilityBeforeBooking {
  all r: Resource |
    r.isAvailable = 1 => some a: Appointment | a.resources = r
}





// <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<< Complex. >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
// 1. No two appointments for the same doctor can overlap in time.
fact NoOverlappingAppointments {
  all a1, a2: Appointment |
    (a1 != a2 and a1.doctor = a2.doctor) implies (
      a1.date != a2.date or
      timeInMinutes[a1.timeSlot.endingTime] <= timeInMinutes[a2.timeSlot.startingTime] or
      timeInMinutes[a2.timeSlot.endingTime] <= timeInMinutes[a1.timeSlot.startingTime])
}

// 2. Doctors must not have back-to-back appointments without a 10-minute gap
fact DoctorAppointmentsHave10MinGap {
  all a1, a2: Appointment |
    (a1 != a2 and a1.doctor = a2.doctor and a1.date = a2.date) implies
      timeInMinutes[a1.timeSlot.endingTime] + 10 <= timeInMinutes[a2.timeSlot.startingTime]
      or timeInMinutes[a2.timeSlot.endingTime] + 10 <= timeInMinutes[a1.timeSlot.startingTime]
}

// 3. Appointments must fall within the doctor’s declared working hours.
fact AppointmentsInDoctorsWorkingHours {
    all a: Appointment |
    some s: a.doctor.assignedShifts | (s.date = a.date) implies
    (timeInMinutes[a.timeSlot.startingTime] >= timeInMinutes[s.startingTime] and
    timeInMinutes[a.timeSlot.endingTime] <= timeInMinutes[s.endingTime])
}

// 4. A nurse cannot be scheduled for night and morning shifts on the same day.
fact NoMorningAndNightShiftForSameNurse {
  all s1, s2: Shift |
    s1 != s2 and // different shifts.
    s1.date = s2.date and // same date.
    ((s1.type = "Morning" and s2.type = "Night") or (s1.type = "Night" and s2.type = "Morning")) implies
      no nurse: Staff | // no staff exists ...
        nurse.type = "Nurse" and // who is a nurse and ...
        nurse in s1.assignedTo and 
        nurse in s2.assignedTo // ... is assigned to both shifts.
}

// 5. A patient’s EHR can only be modified by the assigned doctor.
fact OnlyAssignedDoctorCanModifyEHR {
  all a: Appointment |
    a.patient.ehr.patient = a.patient and
    a.doctor in Doctor
}

// 6. If a patient is transferred from the ward to the ICU, the previous bed must be released.
fact BedReleaseWhenPatientTransferredAndBedType {
  all p: Patient, b1, b2: Bed |
    // Ensure patient p occupies b1 and b2 is empty.
    p.bed = b1 and b2.isOccupied = 0 and
    // When patient is transferred to b2 (ICU), b1 is released (ward).
    p.bed = b2 implies {
      // Ensure that the patient's previous bed is a ward bed (b1 type).
      b1.type = "General Ward" and
      b2.type = "ICU" and // The new bed is ICU.
      b1.isOccupied = 0 and  // Release previous bed.
      b1.assignedPatient = none and  // No longer assigned to any patient.
      b2.isOccupied = 1 and  // The new bed must be occupied.
      b2.assignedPatient = p // The patient is assigned to the new bed.
    }
}

// 7. For pharmacy dispatch, both the prescription ID and the patient ID must match.
fact PharmacyDispatchPrescriptionIDMatch {
  all p: Prescription |
    p.appointment.patient.id = p.appointment.patient.id // prescription is matched to the correct patient.
}

// 8. Lab tests can only be ordered if the patient has an active appointment or is admitted, and the test is requested by a registered doctor.
fact LabTestOrderConditions {
  all lt: LabTest |
    (lt.appointment.status = "Active" or lt.appointment.patient.appointment != none) and // Admitted = has a bed.
    lt.appointment.doctor in Doctor // Ensure that lab tests are ordered only by registered doctors.
}

// 9. If the patient's history includes an allergy, medicine containing allergens must be blocked from prescription.
fact BlockAllergenMedicineFromPrescription {
  all p: Patient, m: Medicine |
    some a: p.ehr.allergies | 
    a.name in m.allergens implies 
    not (m in p.prescription.medicines)
}

// 10. Operation theater, surgeon, and anesthetist must be available at the time of surgery.
fact OperationTheaterAndStaffAvailability {
  all s: Surgery |
    some ot: OperationTheater | ot.id = s.assignedOT and
    some surgeon: Doctor | surgeon = s.appointment.doctor and
    some an: Staff | an = s.anesthetist and
    
    // Check if the surgeon is available during the surgery time slot
    some surgeonShift: surgeon.assignedShifts |
      surgeonShift.date = s.appointment.date and
      timeInMinutes[s.appointment.timeSlot.startingTime] >= timeInMinutes[surgeonShift.startingTime] and
      timeInMinutes[s.appointment.timeSlot.endingTime] <= timeInMinutes[surgeonShift.endingTime] and
    
    // Check if the anesthetist is available during the surgery time slot
    some anesthetistShift: an.assignedShifts |
      anesthetistShift.date = s.appointment.date and
      timeInMinutes[s.appointment.timeSlot.startingTime] >= timeInMinutes[anesthetistShift.startingTime] and
      timeInMinutes[s.appointment.timeSlot.endingTime] <= timeInMinutes[anesthetistShift.endingTime]
}



// Assertion:
assert DoctorCannotHaveMultiplePatients {
  all d: Doctor |
    #({ p: Patient | some a: d.appointments | a.patient = p }) <= 1
}
check DoctorCannotHaveMultiplePatients for 5
